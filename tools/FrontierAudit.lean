import Lean
import Lean.Compiler.LCNF.Level
import Lean.Util.CollectAxioms

/-!
# LeanFrontier formal audit

This executable imports compiled candidate modules, enumerates their exported
LeanFrontier declarations, and reports kernel-derived axiom closures as NDJSON.
The Python receiver owns policy; this tool deliberately reports facts only.
-/

open Lean

/-- A conjecture is a definition whose type is literally `Prop`.

`def c : Prop := P` asserts nothing: the kernel confirms `P` is a well-formed
proposition and no more. That is distinct from a theorem, whose type *is* a
proposition, and it needs no `sorry`, so it crosses the trust boundary at no
cost. Stating is verifiable even when proving is not. -/
private def isConjecture : ConstantInfo → Bool
  | .defnInfo value =>
    match value.type.consumeMData with
    | .sort .zero => true
    | _ => false
  | _ => false

private def rawKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationKind (info : ConstantInfo) : String :=
  if isConjecture info then "conjecture" else rawKind info

private def isTheorem : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

private def hasPrefix (rootName candidateName : Name) : Bool :=
  rootName.isPrefixOf candidateName

private def runInEnv {α : Type} (env : Environment) (action : CoreM α) : IO α :=
  Lean.Core.CoreM.toIO' action { fileName := "<frontier-audit>", fileMap := default } { env := env }

private partial def alphaNormalize : Expr → Expr
  | .forallE _ type body binderInfo => .forallE .anonymous (alphaNormalize type) (alphaNormalize body) binderInfo
  | .lam _ type body binderInfo => .lam .anonymous (alphaNormalize type) (alphaNormalize body) binderInfo
  | .letE _ type value body nonDep => .letE .anonymous (alphaNormalize type) (alphaNormalize value) (alphaNormalize body) nonDep
  | .app function argument => .app (alphaNormalize function) (alphaNormalize argument)
  | .mdata _ expression => alphaNormalize expression
  | .proj typeName index value => .proj typeName index (alphaNormalize value)
  | expression => expression

private def normalizedType (info : ConstantInfo) : Expr :=
  alphaNormalize (Compiler.LCNF.normLevelParams info.type).1

/-- The expression a declaration's fingerprint is taken over.

For a theorem this is its type, the proposition it proves. For a conjecture it
is its *value*: every conjecture's type is literally `Prop`, so type
fingerprints would all collide, and the proposition of interest is the
right-hand side. Taking the value through the same normalization is what lets a
conjecture restating a Mathlib theorem collide with it as a duplicate. -/
private def normalizedStatement (info : ConstantInfo) : Expr :=
  if isConjecture info then
    alphaNormalize (Compiler.LCNF.normLevelParams (info.value?.getD info.type)).1
  else
    normalizedType info

/-- Constant references in an elaborated declaration type.  This deliberately
ignores proof values: the receiver uses these edges only to measure the public
interface graph. -/
private partial def typeDependencies : Expr → List Name
  | .const name _ => [name]
  | .forallE _ type body _ => typeDependencies type ++ typeDependencies body
  | .lam _ type body _ => typeDependencies type ++ typeDependencies body
  | .letE _ type value body _ => typeDependencies type ++ typeDependencies value ++ typeDependencies body
  | .app function argument => typeDependencies function ++ typeDependencies argument
  | .mdata _ expression => typeDependencies expression
  | .proj typeName _ value => typeName :: typeDependencies value
  | _ => []

private partial def exprNodeCount : Expr → Nat
  | .forallE _ type body _ => 1 + exprNodeCount type + exprNodeCount body
  | .lam _ type body _ => 1 + exprNodeCount type + exprNodeCount body
  | .letE _ type value body _ => 1 + exprNodeCount type + exprNodeCount value + exprNodeCount body
  | .app function argument => 1 + exprNodeCount function + exprNodeCount argument
  | .mdata _ expression => 1 + exprNodeCount expression
  | .proj _ _ value => 1 + exprNodeCount value
  | _ => 1

private def hexDigit (value : Nat) : Char :=
  Char.ofNat <| if value < 10 then '0'.toNat + value else 'a'.toNat + value - 10

private def hexEncode (text : String) : String :=
  String.ofList <| text.toUTF8.toList.flatMap fun byte =>
    let value := byte.toNat
    [hexDigit (value / 16), hexDigit (value % 16)]

private def canonicalType (type : Expr) : String :=
  -- `reprStr` can contain physical line breaks which Lean's JSON encoder does
  -- not consistently escape for every Mathlib term. Hex-encoded UTF-8 is
  -- injective and limits the surrounding audit stream to ASCII.
  hexEncode <| reprStr type

private def rawCanonicalType (type : Expr) : String :=
  reprStr type

/-! The hash is only an index prefilter. Python compares `type_canonical` with SHA-256. -/
private def typeHint (type : Expr) : String :=
  toString (hash type)

private def declarationJson (includeAxioms : Bool) (env : Environment) (name : Name) (info : ConstantInfo) : IO Json := do
  let axioms ← if includeAxioms then runInEnv env <| collectAxioms name else pure #[]
  let type := normalizedStatement info
  let canonical := canonicalType type
  return Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("axioms", Json.arr (axioms.map fun axiomName => toJson axiomName.toString)),
    ("type_hint", toJson (typeHint type)),
    ("type_canonical", toJson canonical),
    ("type_dependencies", Json.arr <| ((typeDependencies type).eraseDups.map fun dependency => toJson dependency.toString).toArray),
    ("normalized_term_bytes", toJson (canonical.length / 2))
  ]

private def fingerprintJson (info : ConstantInfo) : Json :=
  let type := normalizedType info
  Json.mkObj [
    ("kind", toJson (declarationKind info)),
    ("type_hint", toJson (typeHint type)),
    ("type_canonical", toJson (canonicalType type))
  ]

private def parseArgs (args : List String) : Bool × List String × Array Import :=
  let all := args.contains "--all"
  let fingerprints := match args.find? (·.startsWith "--match=") with
    | some value => (value.drop "--match=".length).toString.splitOn ","
    | none => []
  let modules := args.filter fun arg => arg != "--all" && arg != "--fingerprints" && arg != "--" && !arg.startsWith "--match="
  let modules := if modules.isEmpty then ["LeanFrontier"] else modules
  (all, fingerprints, modules.toArray.map fun module => { module := module.toName })

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (all, filters, imports) := parseArgs args
  let fingerprints := args.contains "--fingerprints"
  let env ← importModules imports {}
  if all && fingerprints then
    -- The index builder sorts its final JSON itself. Stream the source map
    -- directly here: retaining and sorting every Mathlib theorem can exceed a
    -- standard GitHub runner's memory before any fingerprint is emitted.
    env.constants.forM fun _ info => do
      let type := normalizedType info
      let requested := filters.isEmpty || filters.contains (typeHint type)
      -- Candidates are capped at 64 KiB of normalized term representation.
      -- A term with more than 64 Ki expression nodes cannot match one, so omit
      -- it before expensive pretty serialization.
      if isTheorem info && requested && exprNodeCount type ≤ 65536 then
        let canonical := rawCanonicalType type
        -- A length-prefixed raw UTF-8 payload is safe even when the term's
        -- representation contains line breaks or unusual Unicode.
        IO.println s!"{declarationKind info}\t{typeHint type}\t{canonical.toUTF8.size}"
        IO.print canonical
    return 0
  let selected := env.constants.fold (init := #[]) fun result name info =>
    let requested := filters.isEmpty || filters.contains (typeHint (normalizedType info))
    if (all && isTheorem info && requested) || (!all && hasPrefix `LeanFrontier name) then
      result.push (name, info)
    else
      result
  for (name, info) in selected.qsort fun left right => left.1.quickLt right.1 do
    if all then
      IO.println (fingerprintJson info).compress
    else
      IO.println (← declarationJson true env name info).compress
  return 0

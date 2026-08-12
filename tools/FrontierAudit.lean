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

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

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

private def canonicalType (info : ConstantInfo) : String :=
  reprStr (normalizedType info)

/-! The hash is only an index prefilter. Python compares `type_canonical` with SHA-256. -/
private def typeHint (info : ConstantInfo) : String :=
  toString (hash (normalizedType info))

private def declarationJson (includeAxioms : Bool) (env : Environment) (name : Name) (info : ConstantInfo) : IO Json := do
  let axioms ← if includeAxioms then runInEnv env <| collectAxioms name else pure #[]
  let canonical := canonicalType info
  return Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (declarationKind info)),
    ("axioms", Json.arr (axioms.map fun axiomName => toJson axiomName.toString)),
    ("type_hint", toJson (typeHint info)),
    ("type_canonical", toJson canonical)
  ]

private def parseArgs (args : List String) : Bool × List String × Array Import :=
  let all := args.contains "--all"
  let fingerprints := match args.find? (·.startsWith "--match=") with
    | some value => (value.drop "--match=".length).toString.splitOn ","
    | none => []
  let modules := args.filter fun arg => arg != "--all" && arg != "--" && !arg.startsWith "--match="
  let modules := if modules.isEmpty then ["LeanFrontier"] else modules
  (all, fingerprints, modules.toArray.map fun module => { module := module.toName })

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (all, filters, imports) := parseArgs args
  let env ← importModules imports {}
  let selected := env.constants.fold (init := #[]) fun result name info =>
    let requested := filters.isEmpty || filters.contains (typeHint info)
    if (all && isTheorem info && requested) || (!all && hasPrefix `LeanFrontier name) then
      result.push (name, info)
    else
      result
  for (name, info) in selected.qsort fun left right => left.1.quickLt right.1 do
    IO.println (← declarationJson (!all) env name info).compress
  return 0

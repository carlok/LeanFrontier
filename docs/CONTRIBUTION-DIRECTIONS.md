# LeanFrontier contribution directions

This document is a **non-normative planning aid** for extending the LeanFrontier corpus.

It is not part of the trusted submission contract and it does not authorize a submission by
itself. Before acting on any direction below, re-read the current
[`CONTRACT.md`](../CONTRACT.md) and submitter guidance, fetch current `main`, inspect the
accepted source modules and generated catalogue, search Mathlib and LeanFrontier for duplicate
or equivalent formulations, and revalidate any mathematical literature claim.

The purpose of this document is narrower: preserve useful, adversarially reviewed directions
for making the corpus accumulate into connected, reusable bodies of mathematics rather than a
bag of unrelated theorems. It should describe mathematical opportunities and representation
boundaries, not the state or sequencing of particular contributors' branches or pull requests.

## 1. Selection principle

Prefer a bridge theorem when it does all or most of the following:

- substantively uses two or more accepted LeanFrontier definitions or theorems, rather than
  merely importing their modules;
- expresses a recognized mathematical connection, or creates an abstraction with clear
  independent purpose;
- has plausible downstream consumers after it is merged;
- strengthens the internal dependency graph for mathematical reasons rather than for graph
  aesthetics;
- is not already present in Mathlib or LeanFrontier under an equivalent formulation;
- survives an adversarial boundary review before a candidate is frozen.

A useful test is:

> If this bridge existed, what mathematically natural theorem would become easier or newly
> possible next?

If there is no good answer, do not formalize the bridge merely to create an import edge.

## 2. Current high-value mathematical clusters

The accepted corpus contains several mathematically related groups whose formal dependency
structure is still weaker than their mathematical relationship.

### Rational / Farey / Stern / Ford / Apollonian cluster

Accepted material includes:

- `LeanFrontier.NumberTheory.Mediant`
- `LeanFrontier.NumberTheory.Farey`
- `LeanFrontier.NumberTheory.FordCircle`
- `LeanFrontier.Geometry.FordCircleTangency`
- `LeanFrontier.NumberTheory.SternDiatomic`
- `LeanFrontier.NumberTheory.SternDiatomic.Enumeration`
- `LeanFrontier.NumberTheory.DescartesCircle`
- `LeanFrontier.Geometry.InversiveGeometry`

This is currently the strongest synthesis cluster. In particular, the corpus now contains both
the arithmetic Farey-neighbour criterion for Ford circles and the bridge to Mathlib's actual
`EuclideanGeometry.Sphere.IsExtTangent` predicate.

### Fibonacci / Lucas / recurrence / matrix cluster

Accepted material includes:

- `LeanFrontier.Combinatorics.FibonacciComposition`
- `LeanFrontier.Analysis.FibonacciReciprocal`
- `LeanFrontier.LinearAlgebra.FibonacciMatrix`
- `LeanFrontier.NumberTheory.LucasNumber`
- `LeanFrontier.NumberTheory.HoradamSequence`
- nearby higher-order recurrence modules `Padovan` and `Tribonacci`.

This cluster is mathematically dense but still has room for stronger interfaces between scalar
recurrences and linear algebra.

### Markov / rational-tree cluster

Accepted material includes:

- `LeanFrontier.NumberTheory.MarkovEquation`
- `LeanFrontier.NumberTheory.MarkovTree`
- the Farey / Stern material above.

The accepted Markov-tree development now supplies the local ordered-positive Vieta descent step
`LeanFrontier.MarkovTree.jump_descends_ordered_positive`. What is still missing is a durable
tree/path representation that can carry a full combinatorial correspondence to the
Farey/Stern-Brocot side.

A full Markov/Farey correspondence remains a high-value long-term target, but it must avoid
crossing the Markov uniqueness-conjecture boundary.

## 3. Audited directions — highest priority

### A. Largest Ford circle between Farey neighbours

**Current corpus fit:** ready to investigate.

**Primary parents:**

- `LeanFrontier.NumberTheory.Farey`
- `LeanFrontier.NumberTheory.FordCircle`
- optionally `LeanFrontier.NumberTheory.Mediant` for the explicit mediant witness.

**Mathematical target:**

For positive-denominator Farey neighbours `a/b < c/d`, any fraction `p/q` strictly between
them satisfies `q >= b + d`. Since a Ford-circle radius is `1 / (2*q^2)`, the Ford circle of
the mediant `(a+c)/(b+d)` is the unique largest Ford circle whose rational tangency point lies
strictly between the two neighbours.

A strong statement should include the equality/uniqueness case, not merely a monotone radius
inequality:

- every interior fraction gives radius at most `radius (b+d)`;
- equality forces `q = b+d` and then `p = a+c` by the accepted Farey equality theorem.

**Why this is valuable:**

This composes arithmetic denominator optimality with Ford geometry. Both accepted parents do
essential work. It turns the classical phrase "the mediant is the simplest fraction in the
gap" into the geometric statement "the mediant Ford circle is the largest Ford circle in the
gap."

**Adversarial checks required:**

- positivity assumptions on all denominators;
- representation issue: fractions are numerator/denominator pairs, not quotient types;
- equality of radii must imply equality of positive denominators, not only equality of squares;
- ensure reducible/non-reduced alternate representatives do not break the intended uniqueness
  statement;
- search Mathlib and current LeanFrontier for an equivalent Ford-gap extremal theorem.

**Priority:** A+.

---

### B. Ford–Farey–Descartes configuration

**Current corpus fit:** ready to investigate.

**Primary parents:**

- `Mediant`
- `Farey`
- `FordCircle`
- `FordCircleTangency`
- `DescartesCircle`.

**Mathematical target:**

For a positive-denominator Farey-neighbour pair, the two parent Ford circles and the Ford circle
of their mediant are pairwise externally tangent. Their curvatures are `2*b^2`, `2*d^2`,
and `2*(b+d)^2`; together with curvature `0` for the tangent line, these form a Descartes
quadruple.

The accepted theorem
`LeanFrontier.FordCircle.isExtTangent_euclideanSphere_iff` now supplies the geometric
Ford-circle tangency interface, so the strongest version no longer needs a separate preliminary
bridge to Mathlib's sphere language.

**Important audit result:**

Do **not** submit only the bare identity

`DescartesCircle.IsQuadruple 0 (2*b^2) (2*d^2) (2*(b+d)^2)`.

That algebraic identity is true without the Farey-neighbour hypothesis and would barely compose
the existing theories. The worthwhile theorem must include the actual Farey/Ford geometric
configuration, with tangency or an equivalent meaningful geometric interface.

**Why this is valuable:**

It connects rational approximation / Stern-Brocot insertion to Apollonian circle geometry and
gives `DescartesCircle` a genuine geometric interpretation.

**Priority:** A+.

---

### C. Lucas numbers as characteristic-polynomial data of Fibonacci Q-matrix powers

**Current corpus fit:** ready to investigate.

**Primary parents:**

- `LeanFrontier.LinearAlgebra.FibonacciMatrix`
- `LeanFrontier.NumberTheory.LucasNumber`.

**Existing ingredients:**

- `trace_fibMatrix_pow_succ` gives the trace of a Q-matrix power as a Fibonacci sum;
- `lucas_succ_eq_fib_add_fib` identifies the same Fibonacci sum with a Lucas number;
- `det_fibMatrix_pow` gives determinant `(-1)^n`;
- Mathlib provides the `2 x 2` characteristic-polynomial formula in terms of trace and
  determinant.

**Preferred target:**

Do not stop at the trivial bridge `trace (fibMatrix^n) = lucas n`. Promote it into the
structural statement

`charpoly (fibMatrix^n) = X^2 - C(lucas n) * X + C((-1)^n)`

with the necessary casts and indices stated cleanly.

**Why this is valuable:**

It identifies Lucas numbers as actual linear-algebraic invariants of Fibonacci evolution, not
merely another Fibonacci rewrite. It also creates a useful interface for later eigenvalue,
recurrence, determinant, and Binet-style work.

**Adversarial checks required:**

- index `n=0` and cast conventions over `Int`;
- sign/cast of `(-1)^n`;
- avoid merely restating a Mathlib theorem after rewriting;
- determine whether a trace-only lemma should be public scaffolding or private proof support.

**Priority:** A.

---

### D. General Horadam companion matrix

**Current corpus fit:** high-value infrastructure; verify the live catalogue before
implementation.

**Primary parents:**

- `LeanFrontier.NumberTheory.HoradamSequence`
- `LeanFrontier.LinearAlgebra.FibonacciMatrix`
- later `LucasNumber` as a natural consumer.

The accepted corpus has the general Horadam recurrence and the specialized Fibonacci Q-matrix,
but the abstraction boundary between the two is still a natural place to consolidate reusable
linear-algebraic structure.

**Mathematical target:**

For the Horadam recurrence

`W(n+2) = P*W(n+1) - Q*W(n)`,

define the companion matrix

`A(P,Q) = [[P, -Q], [1, 0]]`.

For the fundamental sequence `U_n = W P Q 0 1 n`, prove an explicit power formula, e.g.

`A(P,Q)^(n+1) = [[U_(n+2), -Q*U_(n+1)], [U_(n+1), -Q*U_n]]`

over an appropriate commutative ring, and connect the recurrence to Mathlib's
`LinearRecurrence` abstraction when that yields a cleaner public interface.

Then show that the existing Fibonacci Q-matrix is the specialization `A(1,-1)`.

**Why this is valuable:**

This creates an abstraction hub rather than a special-case bridge. It can support generalized
Cassini identities, Lucas-like companion sequences, trace/determinant formulas, Chebyshev
specializations, and later Binet-style results.

**Risks / design questions:**

- choose the coefficient type/general ring assumptions carefully;
- decide whether to reuse the existing `Horadam.W` directly or introduce a fundamental
  companion-sequence namespace;
- reuse Mathlib's generic linear-recurrence infrastructure rather than duplicating it;
- preserve the existing `FibonacciMatrix` API rather than replacing it merely for architectural
  neatness.

**Priority:** A+, but larger than a normal bridge contribution.

## 4. Audited directions — worthwhile but secondary

### E. Circular square/domino tilings counted by Lucas numbers

**Primary parents:** `FibonacciComposition` + `LucasNumber`.

Classically, linear square/domino tilings are Fibonacci-counted while circular tilings are
Lucas-counted. A credible Lean development should define a genuine circular tiling object and
decompose it by whether a domino crosses a chosen seam, reducing the cases to existing linear
`oneTwoCompositions` counts.

Do not define the circular object artificially as the disjoint union whose cardinality is
already the desired formula.

**Priority:** A-/B+.

---

### F. Explicit Prouhet power sums from Thue–Morse + PowerSums

**Primary parents:** `ThueMorse` + `PowerSums`.

The accepted Prouhet theorem gives equality of power sums between the two Thue–Morse classes.
`PowerSums` can provide explicit total power sums, e.g. for cubes, so each equal half can be
identified explicitly.

This is a genuine composition of two accepted modules, but its current downstream value is
modest.

**Priority:** B.

---

### G. Maximum Stern-row value is Fibonacci

**Primary parent:** `SternDiatomic`; Fibonacci support would mainly come from Mathlib.

The classical extremal theorem says the maximum of Stern's sequence on an appropriate dyadic
row/block is a Fibonacci number.

**Audit result:** mathematically excellent, but it is a weaker *LeanFrontier bridge* than first
thought. The proof does not naturally need `FibonacciComposition`; rewriting the Fibonacci
value as a composition cardinality would be decorative.

Treat it as a good independent Stern extension, not as a top corpus-synthesis target.

**Priority:** A as mathematics, B as a bridge.

## 5. Dependency-gated / long-term directions

### H. Stern diatomic / Calkin–Wilf to Stern–Brocot representation bridge

**Status:** reformulated; high effort.

**Critical correction:**

Do not claim that increasing-index fractions

`fusc n / fusc (n+1)`

are simply the Stern–Brocot enumeration in the same order. They are naturally the Calkin–Wilf
enumeration. Stern–Brocot contains the same positive rationals in a different tree/order.

A correct bridge should explicitly represent paths/tree nodes and prove the appropriate
transformation (such as path/bit reversal) relating the Calkin–Wilf / Stern-diatomic indexing to
Stern–Brocot mediant paths.

This likely requires new tree/path infrastructure before the final bridge theorem becomes clean.

**Priority:** A mathematical importance, high implementation cost.

---

### I. Markov tree to Farey / Stern–Brocot tree

**Status:** long-term, with the local Markov descent step now accepted.

Classical theory identifies a combinatorial correspondence between the Markov tree and the
Farey/Stern–Brocot tree, allowing Markov numbers/triples to be indexed by rational tree
positions.

The accepted `LeanFrontier.MarkovTree.jump_descends_ordered_positive` supplies an important
local descent theorem. Likely remaining prerequisites include:

- a durable Markov-tree/path representation built around repeated Vieta moves;
- coordinate-permutation handling without theorem padding;
- a termination/root-normalization theorem at the representation level, using the accepted
  strict descent;
- a compatible Farey/Stern–Brocot path representation.

**Critical boundary:**

Do not claim that distinct rational tree positions necessarily yield distinct numerical
Markov-number values. That risks crossing the classical Markov/Frobenius uniqueness conjecture
boundary. A path-preserving/tree correspondence is the safe target.

**Priority:** A+, long-term.

---

### J. Markov Fibonacci branch

**Status:** follow-up to a Markov/Farey tree correspondence.

Classically, a distinguished branch of the Markov tree produces odd-index Fibonacci Markov
numbers. This is a worthwhile consequence once the tree/path framework exists.

Do not force this now merely because LeanFrontier contains Fibonacci modules; without the tree
bridge it naturally depends on Mathlib's `Nat.fib`, not on a substantive LeanFrontier
Fibonacci theorem.

**Priority:** later A-/B+.

---

### K. Descartes reflection and actual inversive geometry

**Status:** hold; current representations are still too far apart.

`DescartesCircle` knows curvatures satisfying an algebraic equation.
`InversiveGeometry` knows anti-Möbius reflection of points across a generalized circle in
`ℂ`.

The genuine Apollonian geometric correspondence needs substantially more structure: oriented
circles, centers/radii or curvature-center coordinates, tangency points/configurations, and the
specific inversion/reflection that replaces one Descartes circle by the alternate completion.

Do not submit a theorem equating the existing two `reflect` functions merely because they
share that name; they act on different mathematical objects and are not directly the same
operation.

**Priority:** hold until representation infrastructure exists.

## 6. Directions deliberately not promoted

The following may be mathematically adjacent but currently lack a sufficiently useful bridge
theorem:

- `Padovan` + `Tribonacci`: both fit higher-order linear-recurrence theory, but no compelling
  direct bridge is known yet;
- `FiniteGroupCharacter` + `ThueMorse`: a Boolean-cube character/Fourier viewpoint exists,
  but the current Thue–Morse theorem is already stronger than the obvious character-sum
  consequence;
- `LogisticMap` + `ThueMorse`: binary symbolic dynamics is related in spirit, but no current
  target clearly composes the accepted statements;
- folder-based bridges such as connecting `FibonacciReciprocal` to `Nesbitt` merely because
  both live under `Analysis` are not acceptable.

Keep isolated modules isolated until a real theorem justifies a connection.

## 7. Per-target research dossier format

Before implementation, create a concise dossier containing:

- exact proposed Lean theorem statement or API shape;
- accepted LeanFrontier prerequisites and exact declarations expected to be reused;
- mathematical source(s) and what they actually establish;
- Mathlib search results for equivalent or supporting theorems;
- intended downstream consumers;
- edge cases / degenerate inputs / sign or representation traps;
- expected proof difficulty and missing infrastructure;
- explicit reason the result is more than a graph-padding import edge;
- go / reformulate / reject decision.

Only after that dossier survives review should implementation begin.

When refreshing this document, describe what is present in the accepted corpus and what
mathematical interfaces are missing. Do not encode contributor-specific branch states,
pull-request queues, or submission sequencing; those are transient and belong in the relevant
issue or pull request, not in a shared mathematical roadmap.

# LeanFrontier contribution directions

This document is a **non-normative planning aid** for extending the LeanFrontier corpus.

It is not part of the trusted submission contract and it does not authorize a submission by
itself. Before acting on any direction below, re-read the current
[`CONTRACT.md`](../CONTRACT.md) and submitter guidance, fetch current `main`, inspect the
accepted source modules and generated catalogue, search Mathlib and LeanFrontier for duplicate
or equivalent formulations, and revalidate any mathematical literature claim.

The purpose of this document is narrower: preserve useful, adversarially reviewed directions
for making the corpus accumulate into connected, reusable bodies of mathematics rather than a
bag of unrelated theorems.

**Completed directions are intentionally removed from this file.** The catalogue, submission
records and receiver observations are the historical record of what landed. Keeping completed
targets here as a sequence of `Status: landed` sections makes the roadmap progressively less
useful and encourages agents to rediscover already-finished work.

Likewise, this file should describe mathematical opportunities and representation boundaries,
not the state or sequencing of particular contributors' branches or pull requests.

## 1. Selection principle

Prefer a target when it does all or most of the following:

- substantively uses accepted LeanFrontier definitions or theorems rather than merely importing
  their modules;
- expresses a recognized mathematical connection, or creates reusable infrastructure with a
  clear independent purpose;
- has plausible downstream consumers after it is merged;
- strengthens the internal mathematical dependency graph for mathematical reasons rather than
  graph aesthetics;
- is not already present in Mathlib or LeanFrontier under an equivalent formulation;
- survives an adversarial boundary review before a candidate is frozen.

A useful test is:

> If this result existed, what mathematically natural theorem would become easier or newly
> possible next?

If there is no good answer, do not formalize the result merely to create an import edge.

A second useful test is now increasingly important because several corpus clusters have matured:

> Is this theorem adding a new interface, or is it only another short corollary of an interface
> LeanFrontier already has?

The latter should usually be left to downstream users.

## 2. Where the accepted corpus now has leverage

### Markov / Farey / Stern-Brocot

The prerequisites that used to block a structural Markov/Farey development are now largely
present.

On the Markov side the corpus has:

- the Markov equation and Vieta involution;
- the ordered-positive local descent theorem;
- bundled `State`, coordinate `Move` and finite `walk`;
- preservation, involutivity and exact reversal of walks;
- global reachability of every positive Markov solution from `(1,1,1)`.

On the rational-tree side it has:

- Farey neighbours and mediants;
- Stern-Brocot path enumeration and interval invariants;
- Calkin-Wilf path enumeration;
- the explicit Calkin-Wilf / Stern-Brocot path-reversal bridge.

The main missing object is no longer “some path representation”. It is the **right oriented
binary Markov-tree representation** whose left/right recursion can be compared cleanly with the
Farey/Stern-Brocot recursion.

### Probability / second-moment methods

The corpus now has a coherent second-moment stack:

- finite weighted Paley-Zygmund;
- a finite-PMF interface;
- a measure-theoretic Paley-Zygmund theorem;
- Cantelli's one-sided inequality;
- the finite-event Chung-Erdos inequality.

Mathlib already supplies first and second Borel-Cantelli results, including the independent-event
second lemma. The useful missing step is therefore not another independent Borel-Cantelli
statement, but an infinite-event theorem that **retains dependence information**, with
Kochen-Stone the natural target.

### Interval dynamics

`LeanFrontier.Dynamics.LogisticMap` already contains the classical semiconjugacy

`h(x) = sin (pi*x/2)^2`

between the full tent map and the logistic map at parameter four, together with iterate
transport, interval invariance, fixed points and a genuine period-two orbit.

On `[0,1]`, however, `h` is a homeomorphism. The accepted result is therefore one structural
step short of the classical topological conjugacy statement.

### Arithmetic topology and number fields

Two accepted modules expose unusually clear infrastructure opportunities:

- `LeanFrontier.Topology.Furstenberg` constructs the evenly spaced topology on `Z`, proves
  arithmetic progressions clopen and proves every nonempty open set infinite;
- `LeanFrontier.NumberTheory.DiscriminantTower` deliberately leaves one explicit proposition
  unresolved and proves a reduction that turns a concrete cyclotomic witness into a proof.

These are better targets for structural continuation than mining mature recurrence modules for
additional special-case identities.

### Mature clusters

The Horadam/Fibonacci/Lucas cluster now has scalar recurrence identities, addition laws,
companion matrices, explicit powers, trace, determinant, characteristic polynomials and
specializations. The Farey/Ford/Descartes cluster likewise already contains several arithmetic-
geometric synthesis theorems.

Treat these as **consumer-ready APIs**, not default sources of easy follow-up submissions.
Further work there should introduce a genuinely new abstraction or solve a new mathematical
problem.

## 3. Highest-priority directions

### A. An oriented Markov tree matching the Farey / Stern-Brocot tree

**Status:** prerequisites are now accepted; representation design is the main problem.

**Primary parents:**

- `LeanFrontier.NumberTheory.MarkovTree`;
- `LeanFrontier.NumberTheory.MarkovTree.Paths`;
- `LeanFrontier.NumberTheory.MarkovTree.Reachability`;
- `LeanFrontier.NumberTheory.SternBrocot` and its interval/path modules;
- optionally the accepted Calkin-Wilf/Stern-Brocot bridge for path conventions.

**Mathematical target:**

Classically, the Markov tree and Farey/Stern-Brocot tree are combinatorially equivalent. The
next useful formal object should make that statement precise **at the tree/path level**, before
talking about numerical Markov labels.

A promising design is an oriented Markov node carrying enough information to distinguish the
two forward children from the parent edge. The raw `State` graph has three involutive moves,
coordinate permutations and immediate backtracking; a binary Farey path does not. The
orientation layer should remove that mismatch rather than hiding it in ad hoc case splits.

A good staged development would aim for:

1. an oriented positive Markov-node type or invariant;
2. deterministic left/right child operations, each realized by an accepted Vieta `Move`;
3. a recursive `List Bool` path map whose erasure is a `MarkovTree.walk`;
4. positivity and Markov-solution preservation along that map;
5. a theorem that the left/right recursion has the same rooted-tree shape as the chosen
   Farey/Stern-Brocot representation.

Only after that representation is stable should one use global reachability to study how much of
the positive Markov solution graph it covers modulo coordinate symmetries.

**Critical boundary:**

Do **not** turn tree-position uniqueness into a claim that the numerical Markov number attached
to a position is injective. The classical Frobenius/Markov uniqueness problem remains a genuine
boundary. A bijection of *constructed tree nodes* or path positions is safe; injectivity of the
maximum-coordinate label is not.

**Why this is valuable:**

This is now the clearest long-term synthesis opportunity in the corpus. It would make the
accepted Markov reachability theorem interact with the already rich rational-tree development
and unlock later branch-specific identities without theorem padding.

**Priority:** A+.

---

### B. Kochen-Stone from Chung-Erdos

**Status:** ready for a serious attempt.

**Primary parents:**

- `LeanFrontier.ProbabilityTheory.chungErdos`;
- the accepted measure-theoretic Paley-Zygmund stack;
- Mathlib's limsup/measure and Borel-Cantelli infrastructure.

**Mathematical target:**

For measurable events `A n` with divergent `sum P(A n)`, prove the Kochen-Stone lower bound

[
P(A_n 	ext{i.o.}) ge
limsup_{N	oinfty}
rac{left(sum_{nle N} P(A_n)ight)^2}
     {sum_{m,nle N} P(A_mcap A_n)}.
]

The accepted finite Chung-Erdos theorem is exactly the finite second-moment estimate needed in
the proof. The substantive new work is the tail/limit passage.

A plausible proof architecture is:

1. apply Chung-Erdos to finite tail unions `union_{m <= i <= N} A i`;
2. compare tail sums with prefix sums using divergence of the first moment;
3. pass `N -> infinity` and then `m -> infinity`;
4. identify the decreasing intersection of tail unions with the event limsup.

**Why this is valuable:**

It turns the finite second-moment inequality into a genuinely infinite dependent-event theorem.
It also provides a natural consumer for Mathlib's existing Borel-Cantelli API without
duplicating the independent-event theorem already present there.

**Adversarial checks required:**

- choose `Real` versus `ENNReal` probability expressions deliberately;
- state denominator-zero and positivity conditions in a form stable under tails;
- verify the exact Mathlib convention for set `limsup`;
- do not smuggle in mutual independence;
- audit whether a pairwise-independent Borel-Cantelli corollary is genuinely absent before
  publishing it.

**Priority:** A.

---

### C. Upgrade the tent/logistic semiconjugacy to a topological conjugacy on `[0,1]`

**Status:** ready; the accepted semiconjugacy already contains the hard dynamical identity.

**Primary parent:** `LeanFrontier.Dynamics.LogisticMap`.

**Mathematical target:**

Restrict

`h(x) = sin (pi*x/2)^2`

to the unit interval and package it as a homeomorphism

`Set.Icc (0 : R) 1 ≃ₜ Set.Icc (0 : R) 1`.

Then express the accepted identity as an actual conjugacy between the subtype tent and logistic
self-maps.

The mathematical content still missing from the current module is that `h` is a continuous
strictly increasing bijection of the unit interval, with continuous inverse. Once packaged as a
homeomorphism, iterate and periodic-point transport should become structural consequences rather
than repeated trigonometric rewrites.

**Downstream consumers:**

- equivalence of periodic-point statements under the conjugacy;
- transport of topological transitivity or related dynamical properties when a suitable Mathlib
  API is available;
- a cleaner foundation for any later formalization of chaos at logistic parameter four.

Do not jump directly to a broad theorem named “logistic map is chaotic” unless every component of
the chosen definition is formalized explicitly.

**Priority:** A.

## 4. High-value infrastructure / larger projects

### D. Resolve the discriminant-tower witness

**Status:** explicit accepted open obligation; high implementation risk.

**Primary parent:** `LeanFrontier.NumberTheory.DiscriminantTower`.

The accepted theorem `loadBearing_of_witness` has already reduced
`CoprimalityIsLoadBearing` to a concrete number-field construction. The intended witness is the
pair of quadratic subfields corresponding to `Q(sqrt 2)` and `Q(sqrt (-2))` inside the
eighth cyclotomic field.

Current Mathlib has substantial cyclotomic number-field and discriminant machinery, including
prime-power cyclotomic discriminant formulas. What is not currently packaged for this exact
application is the complete pair of intermediate fields together with all the facts required by
the reduction.

A useful implementation plan is to treat the following as separate mathematical obligations:

1. choose a concrete `L`, preferably `CyclotomicField 8 Q`;
2. construct the two quadratic intermediate fields explicitly;
3. prove both have degree two;
4. prove their absolute discriminants are eight;
5. prove they are linearly disjoint;
6. prove their supremum is `top`;
7. prove `|discr L| = 256`;
8. apply `loadBearing_of_witness`.

Intermediate lemmas are worth publishing only when they are independently reusable; do not
replace the unresolved theorem by another reduction with differently named hypotheses.

**Why this is valuable:**

Unlike many possible extensions, this closes a proposition that the accepted corpus explicitly
marks unresolved and exercises serious number-field infrastructure.

**Priority:** A for value, high risk/high cost.

---

### E. Make the Furstenberg topology algebraic: addition, negation and finite quotients

**Status:** ready from the accepted base topology.

**Primary parent:** `LeanFrontier.Topology.Furstenberg`.

The evenly spaced topology is not merely a topology with convenient clopen sets. It is the
natural congruence/profinite-style topology on the additive group of integers.

A worthwhile structural development would prove, without globally replacing the ordinary
topology instance on `Z`:

- continuity of negation;
- continuity of addition;
- a clean local `TopologicalAddGroup` interface for `furstenbergTopology`;
- identification of arithmetic progressions with fibers of reduction maps to finite cyclic
  quotients such as `ZMod n`;
- ultimately, a characterization of the topology as the one generated/induced by these finite
  quotient maps.

The last item is substantially more valuable than collecting separation-axiom corollaries one at
a time. It gives a conceptual explanation of the clopen arithmetic-progressions basis and opens a
route toward completion/profinite comparisons later.

**Adversarial checks required:**

- preserve the deliberate choice that `furstenbergTopology` is a named topology rather than the
  global topology instance on `Z`;
- handle the zero modulus/zero step separately and cleanly;
- verify topology-order conventions before stating an “initial/coarsest” characterization;
- search Mathlib's adic/profinite infrastructure again before inventing a competing abstraction.

**Priority:** A-/B+.

---

### F. Close the plain changes into a cyclic adjacent-transposition Gray code

**Status:** worthwhile independent extension; smaller than A-E.

**Primary parent:** `LeanFrontier.ChangeRinging`.

The accepted change-ringing module proves that `rows l`:

- has `(length l)!` rows;
- contains every permutation of a nodup start row exactly once;
- starts at `l`;
- changes adjacent rows by one adjacent transposition.

The natural missing endpoint theorem is that, for at least two bells, the final row is also one
adjacent transposition from the first. Combined with the accepted extent results, this packages
the plain changes as a **cyclic** adjacent-transposition Gray code / Hamiltonian cycle through the
permutations.

The proof should expose the recursive endpoint/parity invariant of `weave` rather than verify
the closing swap by enumeration.

**Why this is valuable:**

It completes the graph-theoretic content already latent in the accepted construction and gives
the change-ringing module a stronger reusable combinatorial statement.

**Priority:** B+.

## 5. Conditional or deliberately deferred directions

### Markov Fibonacci branch

A distinguished branch of the classical Markov tree produces Fibonacci-related Markov numbers.
This becomes a good consequence **after** direction A provides a stable oriented Markov/Farey
path representation. Before then, forcing a Fibonacci theorem onto raw Vieta walks is likely to
produce coordinate bookkeeping rather than reusable mathematics.

### Descartes reflection versus inversive geometry

The corpus still has an algebraic Descartes-curvature representation and a separate
point/generalized-circle inversive-geometry representation. A genuine Apollonian reflection
bridge needs oriented circles or curvature-center coordinates, tangency configurations and the
specific inversion replacing one circle by the alternate Descartes completion.

Do not equate existing operations merely because they are both called “reflection”. Keep this on
hold until the missing representation is designed for an independent reason.

### Calkin-Wilf versus Stern-Brocot traversal order

The accepted path-reversal theorem already supplies the important structural bridge between the
two trees. A further contribution should identify a precise, useful traversal-order theorem
before implementation. “They enumerate the same rationals” is no longer enough.

## 6. Directions deliberately not promoted

The following are currently poor default targets:

- more Horadam/Fibonacci/Lucas identities that are short specializations of the accepted
  companion-matrix/addition APIs;
- `FiniteGroupCharacter` extensions whose main content is already covered by Mathlib's richer
  finite-abelian Fourier/character orthogonality infrastructure;
- direct `Padovan` + `Tribonacci` bridges without a compelling common higher-order recurrence
  API and a concrete downstream theorem;
- `LogisticMap` submissions consisting only of more hand-solved low-period orbits before the
  conjugacy interface in C is built;
- isolated separation-axiom corollaries for the Furstenberg topology when the algebraic/finite-
  quotient structure in E would subsume them conceptually;
- folder-based bridges, such as connecting two modules merely because they live under the same
  top-level namespace.

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

When refreshing this document, describe what is present in the **accepted corpus** and what
mathematical interfaces are missing. Do not encode contributor-specific branch states,
pull-request queues or submission sequencing; those are transient and belong in the relevant
issue or pull request, not in a shared mathematical roadmap.

A roadmap-refresh pull request should also state its own provenance: who or what selected the
directions, which accepted revision was audited, which Mathlib/literature searches informed the
reevaluation, and how much mathematical direction came from the human operator. That provenance
describes the planning process; it is not a receiver-validated mathematical claim.

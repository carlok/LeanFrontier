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

A second test is increasingly important because several corpus clusters are now mature:

> Is this theorem adding a new interface, or is it only another short corollary of an interface
> LeanFrontier already has?

The latter should usually be left to downstream users. A recognizable theorem can still be too
small to deserve a new corpus module when the accepted API plus one Mathlib theorem already
proves it immediately.

A third test applies near open problems:

> Is the proposed module a named mathematical result or a representation with an independently
> useful contract, or is it speculative scaffolding whose only justification is that it might
> help with the conjecture later?

The corpus now contains enough open-problem-adjacent infrastructure that this distinction
matters. Prefer literature-backed intermediate theorems over indefinite machinery accumulation.

Greenfield mathematics remains welcome. Reusing the corpus is evidence of accumulation, not a
requirement to force every theorem into an existing cluster. A standalone result is a good target
when it is mathematically substantial, absent from Mathlib, represented cleanly, and likely to
be reusable later.

### What the receiver's triviality probe can see

The receiver tries a few bounded tactics on each entrypoint, stated as its module writes it:
the module's own imports (minus anything the submission adds), its `open`, `variable` and
notation lines, and its namespace, with Mathlib and the earlier corpus as the only baseline. A
statement built from Mathlib and existing corpus names is therefore really probed, and a
trivial one is rejected. A statement about the submission's own new definitions cannot be
stated from the baseline and is reported `not elaborated`; that is not evidence of depth. See
the [threat model](threat-model.md).

## 2. Where the accepted corpus now has leverage

This section describes the accepted corpus at the audited revision recorded in Section 8. It
deliberately ignores unmerged pull requests.

### Arithmetic topology: Furstenberg topology and the profinite completion

The Furstenberg cluster now reaches Mathlib's profinite machinery. The corpus has:

- the named topology `Int.furstenbergTopology`, its arithmetic-progression basis, clopen
  congruence classes, separation and absence of isolated points;
- continuity of addition and negation, and the named `furstenbergAddGroupTopology`;
- `furstenbergTopology_eq_finiteQuotientTopology` (all nonzero cyclic quotients `ZMod n`);
- the classification of finite-index additive subgroups of `ℤ` as `nℤ`, with the quotient
  equivalence to `ZMod n`;
- `furstenbergTopology_eq_genericFiniteQuotientTopology` (all of Mathlib's generic
  finite-index quotients);
- `furstenbergTopology_eq_induced_profiniteCompletion` and
  `isDenseEmbedding_furstenbergProfiniteMap`: the topology induced by Mathlib's canonical map
  into the additive profinite completion is the Furstenberg topology, and the map is a dense
  embedding.

The topology comparison is complete. What remains is the completion statement itself: that the
profinite completion *is* the completion of the Furstenberg topological group (Direction C).

### Rational trees, Euclidean algorithms and continued fractions

The rational-tree cluster now has its classical dictionary with Euclid's algorithm:

- Stern's diatomic sequence, Calkin-Wilf and Stern-Brocot paths, interval bounds, mediant
  invariants and the path-reversal bridge;
- canonical maximal runs of a path, each recording one Euclidean quotient (`RunLength`);
- a whole-path run-length encoding with exact reconstruction (`runLengthEncode`,
  `expandRuns_runLengthEncode`);
- the complete Euclidean quotient sequence of a path's pair (`euclideanRunQuotients_pair`);
- Mathlib's `GenContFract.of` of a path's rational, identified with the finite simple continued
  fraction of its run quotients (`genContFract_pair`, with the leading-zero convention for
  rationals below one).

Two gaps remain. First, `runLengthEncode` and `pathQuotients` were written independently and
peel runs with the same recursion; nothing yet relates them. Second, the dictionary stops at
coefficients: the **convergents** of the continued fraction, and Mathlib's determinant identity
for consecutive convergents, have not been connected to the Stern-Brocot interval bounds and
the corpus's `Mediant.crossDet` (Direction B).

### Interval dynamics

The dynamics cluster now has both components that usually enter a definition of chaos:

- the full tent, logistic and Ulam-von Neumann maps, with `ulamHomeomorph` and the exact
  conjugacy between the tent and logistic self-maps of `[0,1]`;
- topological transitivity of both flows (`tentMapFlow_isTopologicallyTransitive`,
  `logisticMapFlow_isTopologicallyTransitive`), using Mathlib's `Dynamics.Transitive`;
- density of periodic points for both maps (`dense_periodicPts_tentMapIcc`,
  `dense_periodicPts_logisticMapIcc`).

Mathlib (at the pinned release) has no notion of sensitive dependence on initial conditions and
no Devaney-style chaos predicate. That is the next interface (Direction A).

### Cyclotomic eight and explicit quadratic subfields

This cluster reached its structural endpoint: an explicit eighth cyclotomic field with
generators for (sqrt2), (sqrt{-2}) and (i), their minimal polynomials, the discriminant witness
and the resolved `CoprimalityIsLoadBearing`, the Galois group identified as the Klein four
group (`cyclotomicEight_galoisGroup_isKleinFour`) and exactly three quadratic intermediate
fields (`cyclotomicEight_quadraticFields_card`). It should now be consumed, not mined (see the
mature-cluster list).

### Descartes, Ford circles and inversive geometry

The representation gap has narrowed:

- algebraic Descartes quadruples, with the four Vieta reflections packaged as one indexed
  linear map preserving the Descartes form (`descartesForm_curvatureReflection`);
- curvature-center circles in `ℂ` with an external-tangency predicate, lossless conversion to
  Mathlib's spheres, agreement with `Sphere.IsExtTangent`, and a Ford-circle specialization
  (`isExternallyTangent_iff_toSphere`, `isExternallyTangent_curvatureCircle_iff`);
- generalized-circle Hermitian forms and anti-Möbius reflection in `InversiveGeometry`.

Still missing: a geometric Descartes configuration (four mutually tangent curvature-center
circles) proved to satisfy the algebraic relation, and the geometric meaning of a Vieta
reflection (Direction D).

### Markov / Farey / Stern-Brocot

This cluster has changed the most. The corpus now contains, among other things:

- the Markov equation, Vieta moves, local descent and global reachability;
- bundled states, finite walks and exact walk reversal;
- an oriented binary Markov tree;
- the Stern-Brocot path bridge, branch coverage and cyclic symmetry;
- injectivity of the full Markov state along the canonical tree;
- Fibonacci-spine formulas;
- the formal statement of the Frobenius/Markov uniqueness conjecture and its reduction to the
  canonical Stern-Brocot branch;
- monotone Markov-number labels, common-ancestor and first-divergence interfaces;
- re-rooted subtrees and exact child-label algebra;
- pairwise coprimality, sum-of-squares divisibility, square roots of (-1) modulo Markov
  numbers, mod-four information and collision factorization machinery.

This is now a **mature research substrate adjacent to an open conjecture**, not a default source
of roadmap-sized infrastructure. Further work should be justified by a named classical theorem,
a known restricted uniqueness case, or a literature-backed reduction with a clearly bounded
claim. The roadmap should not reward adding one more lemma merely because it may someday help
with uniqueness.

As an example of the new threshold, the statement that every accepted oriented Markov number is
a sum of two squares is mathematically recognizable, but the accepted modular-root theorem plus
Mathlib's `Nat.eq_sq_add_sq_of_isSquare_mod_neg_one` already makes it essentially a direct
consumer corollary. That is useful downstream mathematics, but not by itself a high-priority new
interface.

### Mature clusters that should normally be consumed, not mined

Several other areas now have enough infrastructure that easy follow-ups should not be default
targets:

- Horadam/Fibonacci/Lucas: scalar recurrences, addition laws, companion matrices, explicit
  powers, trace, determinant and characteristic polynomials;
- probability: finite, PMF and measure-theoretic Paley-Zygmund; Cantelli; Chung-Erdos;
  Kochen-Stone; pairwise Borel-Cantelli;
- change ringing: complete permutation extent plus cyclic adjacent-transposition closure;
- finite variance: the variance identity and Laguerre-Samuelson consequence;
- finite-group characters: the corpus has a concrete orthogonality layer while Mathlib has a
  substantially richer general Fourier/character framework;
- Ford/Farey local arithmetic and geometry: enough low-level determinant and tangency lemmas
  already exist that future additions should express a genuinely new synthesis;
- the eighth cyclotomic field: generators, Galois group and quadratic subfields are complete.

## 3. Highest-priority directions

### A. Sensitive dependence and a Devaney package for the tent and logistic maps

**Status:** topological transitivity and dense periodic points are accepted for both maps;
Mathlib has `Dynamics.Transitive` but no sensitivity notion.

**Primary parents:** `LeanFrontier.Dynamics.LogisticTransitivity` and the periodic-density
module; `LeanFrontier.Dynamics.LogisticConjugacy`.

**Mathematical target:**

1. define sensitive dependence on initial conditions for a map of a metric space, stating the
   definition explicitly (there is no Mathlib notion to reuse);
2. prove the theorem of Banks, Brooks, Cairns, Davis and Stacey (*On Devaney's definition of
   chaos*, Amer. Math. Monthly 99, 1992): on an infinite metric space, a topologically
   transitive map with dense periodic points has sensitive dependence;
3. apply it to the tent and logistic maps, and package the three components under an explicitly
   stated Devaney definition.

The general theorem in step 2 is the valuable part: it is classical, reusable beyond these two
maps, and turns the two accepted properties into a third without a map-specific computation.

**Adversarial checks required:**

- state which definition of chaos is meant; texts differ, and the sensitivity constant matters;
- the infinite-space hypothesis is necessary (a single periodic orbit is transitive with dense
  periodic points but not sensitive); include it rather than hiding it in the interval case;
- reuse Mathlib's transitivity predicate and `Function.periodicPts`; do not redefine them;
- search the pinned Mathlib again for any sensitivity notion before introducing one.

**Priority:** A.

---

### B. Stern-Brocot convergents, the determinant identity, and one recursion

**Status:** coefficients are connected (`genContFract_pair`); convergents are not.

**Primary parents:** `LeanFrontier.NumberTheory.SternBrocot.ContinuedFraction`,
`QuotientSequence`, `RunEncoding`, `Intervals`; `LeanFrontier.NumberTheory.Mediant`;
Mathlib's `Algebra.ContinuedFractions.Determinant` and convergent/continuant APIs.

**Mathematical target:**

1. relate the convergents of a path's continued fraction to the Stern-Brocot interval bounds
   along that path (consecutive convergents bound the path's rational, as the interval
   endpoints do);
2. show that Mathlib's determinant identity for consecutive convergents is the corpus's
   `Mediant.crossDet = 1` invariant for neighbouring bounds, rather than reproving either;
3. as a small, self-contained piece: prove that `pathQuotients` is the run lengths of
   `runLengthEncode` with one added to the last (for nonempty paths), so the two independently
   accepted recursions are formally the same object.

**Adversarial checks required:**

- convergents of a finite continued fraction include the terminal one; align indices with the
  path's length and the leading-zero convention of `regularCoefficients`;
- do not introduce a third encoding of runs; consume the two that exist;
- signs: the determinant identity alternates; state which orientation matches `crossDet`.

**Priority:** A for 1–2; item 3 is small but closes a known duplication.

---

### C. The profinite completion is the completion of the Furstenberg group

**Status:** the canonical map `ℤ → Ẑ` is accepted as a dense embedding inducing the Furstenberg
topology.

**Primary parents:** `LeanFrontier.Topology.FurstenbergProfiniteCompletion`;
`furstenbergAddGroupTopology`; Mathlib's `Topology.UniformSpace.AbstractCompletion` and
`Topology.Algebra.Category.ProfiniteGrp.Completion`.

**Mathematical target:** give `ℤ` the uniformity of the Furstenberg additive group topology,
show that `Ẑ` with the canonical map is an `AbstractCompletion` of it (complete, separated,
uniformly inducing, dense range), and obtain the comparison equivalence with Mathlib's
`UniformSpace.Completion` from `AbstractCompletion.compareEquiv`.

**Adversarial checks required:**

- the uniformity must be the group uniformity of `furstenbergAddGroupTopology`, kept local;
  do not install a global instance on `ℤ`;
- dense embedding is accepted, but uniform inducing is a stronger statement: prove it;
- completeness of `Ẑ` should come from Mathlib's compactness of profinite groups, not be
  reproved.

**Priority:** B+.

---

### D. A geometric Descartes configuration

**Status:** curvature quadruples with packaged reflections and curvature-center circles with
tangency are accepted, in separate modules.

**Primary parents:** `LeanFrontier.NumberTheory.DescartesCircle`,
`LeanFrontier.Geometry.CurvatureCenter`, `LeanFrontier.Geometry.InversiveGeometry`.

**Mathematical target:**

1. define four mutually externally tangent curvature-center circles as a configuration;
2. prove that their curvatures satisfy the accepted Descartes form;
3. prove that the second circle tangent to three given ones has the curvature given by the
   accepted Vieta reflection;
4. only then, relate that replacement to inversion in the circle through the three tangency
   points.

**Critical boundary:** `DescartesCircle.reflect` acts on curvatures and
`InversiveGeometry.reflect` on points. Any theorem relating them must go through the
configuration in step 1, not through the shared name.

**Priority:** B+; high representation risk.

## 4. Conditional / research-only directions

### Markov uniqueness program

The corpus now has enough standard groundwork that “continue building machinery” is not a
sufficient target description.

Further submissions in this direction should satisfy at least one of these:

- formalize a named theorem from the Markov-uniqueness literature;
- prove a classical restricted uniqueness case with an explicit arithmetic hypothesis;
- turn an existing accepted reduction into a strictly stronger reduction with a measurable
  loss of cases;
- package a genuinely reusable arithmetic object used by more than the conjecture itself.

A proposed theorem should state clearly how it sits relative to the open
`UniquenessConjecture`. No submission should imply that tree-position injectivity, full-state
injectivity, modular restrictions or collision factorization resolve injectivity of the single
maximum-coordinate label.

Do not add another branch-separation invariant solely because it holds experimentally. At this
stage, literature search and a proof-level reason for the invariant come before formalization.

### Apollonian integral orbits

After Direction D supplies a geometric configuration, arithmetic questions about integral
Descartes quadruples, orbit preservation, primitive packings or congruence restrictions become
natural. Do not start them on the four-scalar representation alone.

## 5. Directions deliberately not promoted

The following are currently poor default targets:

- more Markov scaffolding without a named classical theorem or bounded restricted result;
- the bare corollary that a Markov number is a sum of two squares, unless it is part of a
  stronger reusable arithmetic interface;
- more Horadam/Fibonacci/Lucas identities that are short specializations of accepted recurrence
  and companion-matrix APIs;
- a graph-theoretic restatement of cyclic change ringing that adds only a new name for the
  already accepted adjacent-swap cycle;
- isolated separation-axiom corollaries for the Furstenberg topology now that its additive and
  finite-quotient structures are accepted;
- `FiniteGroupCharacter` extensions whose content is already available more generally in
  Mathlib's finite-abelian Fourier/character theory;
- direct `Padovan` + `Tribonacci` bridges without a compelling higher-order recurrence
  abstraction and a concrete theorem that consumes it;
- broad “chaos” declarations for the logistic map that do not specify and prove the component
  properties;
- direct equality between Descartes and inversive `reflect` operations without a geometric
  circle bridge;
- additional Calkin-Wilf/Stern-Brocot statements that only say the trees enumerate the same
  rationals; the accepted path-reversal theorem already captures that level of structure;
- folder-based bridges, such as connecting two modules merely because they live under the same
  top-level namespace;
- a further recursion over Stern-Brocot runs that does not reuse `runLengthEncode` or
  `pathQuotients`;
- further topology comparisons for the Furstenberg topology: it is now identified with both the
  finite-quotient and the profinite-completion topologies.

Keep isolated modules isolated until a real theorem justifies a connection.

## 6. Greenfield work while mature clusters cool

This roadmap is not an exclusive work queue. In particular, a mature cluster may need time for
review, literature work or representation design while unrelated mathematics can still extend
the frontier.

For a greenfield theorem, prefer:

- a classical result with a stable statement and identifiable source;
- no equivalent theorem in the pinned Mathlib release;
- enough proof content that the submission is not a disguised exercise;
- a representation likely to support at least one natural follow-up theorem;
- a subject not chosen merely because it is easy to formalize in isolation.

A greenfield module does not need to import an existing LeanFrontier theorem. If it later gains a
consumer, that is stronger evidence of organic accumulation than forcing a connection at birth.

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

## 8. Provenance of this refresh

This refresh was prepared on 9 October 2026 against accepted LeanFrontier revision
`d1e5c4c7c29e6dddaf260d9f3d03e1a360fb6a91` (110 modules), with the pinned dependency policy Mathlib `v4.34.1`.

It was written by Claude (Claude Code, Anthropic) acting as maintainer, after the human operator
approved "refresh the roadmap" as a backlog item without prescribing directions. The previous
refresh (27 September) had ranked five directions; the audit compared each against the accepted
submissions since then (`experiments/accumulation.csv`, the catalogue and the claims) and found
A and B landed through their main stages, C landed, D complete, and E landed through its first
three stages. The new directions are the unfinished stages of those (B, C, D here), and the
conditional "transitivity to chaos" direction, whose two prerequisites are now accepted (A).

Searches in the pinned Mathlib: `Mathlib/Dynamics` has `Transitive` but no sensitivity or
Devaney notion; `Topology/UniformSpace/AbstractCompletion` provides `compareEquiv`;
`Algebra/ContinuedFractions/Determinant` provides the convergent determinant identity;
`Topology/Algebra/Category/ProfiniteGrp/Completion` provides the profinite completion used by
the accepted modules. The literature reference in Direction A is Banks, Brooks, Cairns, Davis
and Stacey, Amer. Math. Monthly 99 (1992). These are planning notes, not receiver-validated
claims; re-check them before acting.

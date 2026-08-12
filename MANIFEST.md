# Freedom Above the Kernel - A Machine Mathematics Manifesto.

Formal mathematics makes possible a distinction that was historically difficult to sustain: the distinction between mathematical validity and human mathematical understanding.

A machine-generated proof need not be accepted on authority. Its correctness can be checked independently by a small trusted kernel. Consequently, requiring a human contributor to understand and defend every generated proof is no longer logically necessary for establishing formal validity. It may remain essential for a human-oriented library such as Mathlib, where maintainability, exposition, API design, and mathematical judgment are part of the project's purpose. It need not, however, be a universal condition on the existence of formal mathematics.

This suggests a complementary experiment.

Let machines perform mathematics under almost unrestricted conditions, while maintaining an exceptionally narrow formal trust boundary. They may formulate statements, introduce definitions, construct auxiliary theories, prove intermediate results, and build indefinitely on earlier machine-generated mathematics. Their work need not remain close to the organization, abstractions, or proof strategies already present in Mathlib.

The final requirement is absolute rather than interpretive: every accepted declaration must be accepted by the Lean kernel, contain no incomplete proof, and depend transitively on no axioms outside the project's explicitly permitted foundation. Mathlib provides the principal mathematical substrate; machine-generated mathematics may extend arbitrarily far above it.

The governing principle is therefore:

**Freedom above the kernel; rigidity below it.**

The purpose of such a repository would not primarily be to produce another curated mathematical library. It would provide a persistent environment in which machine mathematics can accumulate, depend on itself, diverge from existing human organization, and potentially reconnect with established mathematics.

This changes the object of study. The interesting unit is no longer only the individual theorem. It is the evolving dependency graph of machine-generated mathematics.

Depth from Mathlib, reuse of machine-generated lemmas, emergence of machine-created abstractions, independent rediscovery, convergence between different agents, formation of isolated subtheories, and eventual connections back to established results can all be measured without imposing them as admission requirements.

A bottom-up system that systematically extends the immediate neighborhood of Mathlib and a top-down system that begins with an external mathematical objective represent different experimental regimes. Both should be permitted and recorded. The latter is particularly significant because the machine must choose its own mathematical route while eventually grounding the complete construction in the trusted formal substrate.

The repository would therefore make an unusual trade.

It would impose almost no criterion of mathematical taste, but an extremely strict criterion of formal validity.

It would permit mathematics that no human currently understands, while refusing mathematics that the kernel cannot verify.

It would tolerate triviality, redundancy, awkward abstractions, and failed conceptual directions because filtering them manually would reintroduce human mathematical judgment into the experiment. Such properties should instead be measured, ranked, and studied.

The resulting corpus may contain enormous regions of mathematically uninteresting material. That possibility is not an objection to the experiment; it is one of the hypotheses the experiment can test.

The stronger possibility is that sufficiently capable systems will not merely generate isolated formal consequences. They may begin to construct reusable internal theories: machine-created definitions supporting machine-created lemmas, which support deeper results, which are subsequently reused by other systems. Such structures may reproduce familiar human mathematics, remain alien but sterile, or expose abstractions and connections that are useful precisely because no human imposed them in advance.

The project would exist to find out which of these possibilities occurs.


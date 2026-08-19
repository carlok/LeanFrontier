import LeanFrontier.NumberTheory.SylvesterSequence

/-!
# Receiver probe

Not mathematics anyone needs. Two literal variants of an already-accepted
statement, added to check that the family detector counts members the corpus
already holds. Before #103 the counter reset per submission, so two new members
scored 2 and were admitted. To be closed unmerged.
-/

namespace LeanFrontier.Probe

open LeanFrontier.Nat

/-- A weaker literal variant of the accepted `two_le_sylvesterNumber`. -/
theorem one_le_sylvesterNumber_probe (n : ℕ) : 1 ≤ sylvesterNumber n :=
  Nat.le_of_succ_le (two_le_sylvesterNumber n)

/-- A weaker one still. -/
theorem zero_le_sylvesterNumber_probe (n : ℕ) : 0 ≤ sylvesterNumber n :=
  Nat.zero_le _

end LeanFrontier.Probe

import LeanFrontier.NumberTheory.SternBrocot.QuotientRunBridge
import Mathlib.Tactic

/-!
# Stern–Brocot depth and the sum of continued-fraction digits

A positive rational occupies a unique node of the Stern–Brocot tree. Its
root-to-node path is a Boolean word, and the accepted continued-fraction
dictionary associates to that path the coefficients of its regular continued
fraction (including the conventional leading zero below one).

The **depth formula** states that the sum of those coefficients is exactly
one greater than the number of edges in the path. Thus the sum of the
Euclidean division quotients measures the complexity of the tree address.

The proof consumes the accepted canonical run encoding, its exact
reconstruction theorem, and the quotient/run bridge: each maximal run
contributes its own length, except that Euclid's terminal quotient has
one extra unit. The leading zero does not affect the sum.
-/

namespace LeanFrontier.SternBrocot

/-- Expanding encoded constant runs gives a word whose length is exactly
the sum of the encoded run lengths. -/
private theorem sum_run_lengths (runs : List (Bool × ℕ)) :
    (runs.map Prod.snd).sum = (expandRuns runs).length := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      rcases run with ⟨dir, k⟩
      simp [expandRuns, ih]

/-- Incrementing the last entry of a nonempty list of natural numbers
increases its sum by exactly one. -/
private theorem sum_modifyLast_succ (xs : List ℕ) (hne : xs ≠ []) :
    (List.modifyLast Nat.succ xs).sum = xs.sum + 1 := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x ys ih =>
      cases ys with
      | nil =>
          have hsingle : List.modifyLast Nat.succ [x] = [Nat.succ x] := by
            simpa using (List.modifyLast_concat Nat.succ x [])
          simp [hsingle, Nat.succ_eq_add_one]
      | cons y ys =>
          have htail : (y :: ys : List ℕ) ≠ [] := by simp
          have hstep :
              List.modifyLast Nat.succ (x :: y :: ys) =
                x :: List.modifyLast Nat.succ (y :: ys) := by
            simpa using
              (List.modifyLast_append_of_right_ne_nil
                Nat.succ [x] (y :: ys) htail)
          rw [hstep]
          simp only [List.sum_cons]
          have hrec := ih htail
          simp only [List.sum_cons] at hrec
          omega

/-- The sum of the symmetric Euclidean quotients is the number of edges
in the Stern–Brocot address, plus one, including the root convention. -/
private theorem pathQuotients_sum_eq_length_succ (path : List Bool) :
    (pathQuotients path).sum = path.length + 1 := by
  by_cases hnil : path = []
  · subst path
    simp [pathQuotients]
  · let lengths := (runLengthEncode path).map Prod.snd
    have hnonempty : lengths ≠ [] := by
      cases path with
      | nil => exact (hnil rfl).elim
      | cons dir tail => simp [lengths, runLengthEncode]
    calc
      (pathQuotients path).sum =
          (List.modifyLast Nat.succ lengths).sum := by
            rw [pathQuotients_eq_runLengthEncode path hnil]
      _ = lengths.sum + 1 := sum_modifyLast_succ lengths hnonempty
      _ = path.length + 1 := by
            dsimp [lengths]
            rw [sum_run_lengths, expandRuns_runLengthEncode]

/-- **Stern–Brocot depth formula.** The sum of the coefficients of the
regular continued fraction of the rational indexed by `path` equals
`path.length + 1`. For rationals below one, the conventional initial
zero is included but does not change the sum.

Combined with `genContFract_pair`, this identifies the exact number of
Stern–Brocot edges with the sum of Mathlib's computed regular continued-
fraction coefficients minus one. -/
theorem regularCoefficients_sum_eq_length_succ (path : List Bool) :
    (regularCoefficients path).sum = path.length + 1 := by
  rw [regularCoefficients_runs]
  cases path with
  | nil =>
      simpa using pathQuotients_sum_eq_length_succ ([] : List Bool)
  | cons dir tail =>
      cases dir
      · simpa using pathQuotients_sum_eq_length_succ (false :: tail)
      · simpa using pathQuotients_sum_eq_length_succ (true :: tail)

end LeanFrontier.SternBrocot

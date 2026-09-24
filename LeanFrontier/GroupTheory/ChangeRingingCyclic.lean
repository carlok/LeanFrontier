import LeanFrontier.GroupTheory.ChangeRinging
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Cyclic closure of Stedman's plain changes

The accepted change-ringing development proves that `rows l` lists every permutation exactly
once (for a nodup start row), starts at `l`, and changes adjacent rows by a single adjacent
transposition.  The remaining graph-theoretic endpoint is cyclic closure: for at least two bells,
the last row is also one adjacent transposition from the first.

The recursive invariant is simple but hidden inside `weave`.  Starting a weave in the forward
direction, an even number of shorter rows makes the hunting direction return to forward before
the final block.  Consequently the final inserted bell sits at the front of the final shorter
row.  Since `rows l` has `(length l)!` rows, that number is even as soon as `length l ≥ 2`.

Inducting on the prefix then gives an exact endpoint formula:

`rows (p ++ [x, y])` ends at `p ++ [y, x]`.

Thus the final change is always the transposition of the last two bells of the starting row.
Combined with the accepted extent, nodup, head, and chain theorems, this closes the plain changes
into a cyclic adjacent-transposition Gray code.
-/

namespace LeanFrontier.ChangeRinging

open List

variable {α : Type*}

private theorem hunt_ne_nil (a : α) (b : Bool) (r : List α) :
    hunt a b r ≠ [] := by
  cases b <;> simp [hunt, permutations'Aux_ne_nil]

private theorem weave_ne_nil (a : α) (b : Bool) (rs : List (List α)) :
    weave a b rs ≠ [] ↔ rs ≠ [] := by
  cases rs with
  | nil =>
      simp
  | cons r rs =>
      simp only [List.cons_ne_nil, iff_true, weave_cons]
      exact List.append_ne_nil_of_left_ne_nil (hunt_ne_nil a b r)

private theorem getLast?_weave_true_of_even
    (a : α) (rs : List (List α))
    (heven : Even rs.length) :
    (weave a true rs).getLast? = rs.getLast?.map (cons a) := by
  induction rs using List.twoStepInduction with
  | nil =>
      rfl
  | singleton r =>
      simp at heven
  | cons_cons r s rs ih ihCons =>
      have heven_rs : Even rs.length := by
        simpa [parity_simps] using heven
      by_cases hrs : rs = []
      · subst rs
        have hhunt : hunt a false s ≠ [] :=
          hunt_ne_nil a false s
        rw [weave_cons, weave_cons, weave_nil, append_nil,
          getLast?_append_of_ne_nil _ hhunt,
          getLast?_hunt_false]
        rfl
      · have hweave : weave a true rs ≠ [] :=
          (weave_ne_nil a true rs).2 hrs
        have htail :
            hunt a false s ++ weave a true rs ≠ [] :=
          List.append_ne_nil_of_right_ne_nil hweave
        simp only [weave_cons, Bool.not_true, Bool.not_false]
        rw [getLast?_append_of_ne_nil _ htail,
          getLast?_append_of_ne_nil _ hweave,
          ih heven_rs]
        cases rs with
        | nil =>
            contradiction
        | cons t ts =>
            rw [getLast?_cons_cons]

private theorem even_length_rows_of_two_le
    (l : List α) (h : 2 ≤ l.length) :
    Even (rows l).length := by
  rw [length_rows, even_iff_two_dvd]
  exact Nat.dvd_factorial (by decide : 0 < 2) h

/-- The exact endpoint of the plain changes: if the starting row is written as a prefix followed
by two final bells, the last row is obtained by swapping precisely those final two bells. -/
theorem rows_append_pair_getLast (p : List α) (x y : α) :
    (rows (p ++ [x, y])).getLast? = some (p ++ [y, x]) := by
  induction p with
  | nil =>
      rfl
  | cons z p ih =>
      have hlen : 2 ≤ (p ++ [x, y]).length := by
        simp
      have heven :
          Even (rows (p ++ [x, y])).length :=
        even_length_rows_of_two_le (p ++ [x, y]) hlen
      rw [cons_append, rows_cons,
        getLast?_weave_true_of_even z (rows (p ++ [x, y])) heven,
        ih]
      simp

private theorem exists_append_pair_of_two_le_length
    (l : List α) (h : 2 ≤ l.length) :
    ∃ p x y, l = p ++ [x, y] := by
  have hrev : 2 ≤ l.reverse.length := by
    simpa using h
  cases hr : l.reverse with
  | nil =>
      have hlen : l.length = 0 := by
        have hlen' := congrArg List.length hr
        simpa using hlen'
      omega
  | cons x xs =>
      cases xs with
      | nil =>
          have hlen : l.length = 1 := by
            have hlen' := congrArg List.length hr
            simpa using hlen'
          omega
      | cons y rs =>
          refine ⟨rs.reverse, y, x, ?_⟩
          calc
            l = l.reverse.reverse := by simp
            _ = (x :: y :: rs).reverse := by rw [hr]
            _ = rs.reverse ++ [y, x] := by simp

/-- For every start row with at least two bells, the last row of the plain changes differs from
the first by one adjacent transposition.  Together with `head_rows` and
`isChain_adjSwap_rows`, this is the cyclic-closing edge of the plain-changes Gray code. -/
theorem exists_last_adjSwap_first_of_two_le_length
    (l : List α) (h : 2 ≤ l.length) :
    ∃ last,
      (rows l).getLast? = some last ∧ AdjSwap last l := by
  obtain ⟨p, x, y, rfl⟩ := exists_append_pair_of_two_le_length l h
  refine ⟨p ++ [y, x], rows_append_pair_getLast p x y, ?_⟩
  exact ⟨p, [], y, x, by simp, by simp⟩

end LeanFrontier.ChangeRinging

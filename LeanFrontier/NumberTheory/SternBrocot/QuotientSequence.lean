import LeanFrontier.NumberTheory.SternBrocot.RunLength
import Mathlib.Tactic

/-!
# Euclidean quotient sequences of Stern-Brocot paths

A single maximal Stern-Brocot run is already known to record one Euclidean quotient. This module
iterates that arithmetic statement across a whole path.

The function `euclideanRunQuotients` is the symmetric Euclidean algorithm on a positive pair: at
each step it divides the larger coordinate by the smaller and recurses on the remainder. Thus it
omits the conventional leading zero for a rational below one; that zero can be restored later when
identifying these quotients with regular continued-fraction coefficients.

The function `pathQuotients` recursively peels the accepted canonical initial run of a
Stern-Brocot path. Nonterminal runs contribute their length, while the terminal run contributes
one more than its length, exactly matching the endpoint convention already proved in
`initialRun_euclidean_step`.

The main theorem identifies these two complete quotient sequences.
-/

namespace LeanFrontier.SternBrocot

/-- Euclidean quotients obtained by repeatedly dividing the larger positive coordinate by the
smaller. If either coordinate is zero, the process stops. -/
def euclideanRunQuotients : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _, 0 => []
  | a + 1, b + 1 =>
      if a + 1 < b + 1 then
        (b + 1) / (a + 1) ::
          euclideanRunQuotients (a + 1) ((b + 1) % (a + 1))
      else
        (a + 1) / (b + 1) ::
          euclideanRunQuotients ((a + 1) % (b + 1)) (b + 1)
termination_by a b => a + b
decreasing_by
  · have hmod : (b + 1) % (a + 1) < a + 1 := Nat.mod_lt _ (by omega)
    omega
  · have hmod : (a + 1) % (b + 1) < b + 1 := Nat.mod_lt _ (by omega)
    omega

private theorem euclideanRunQuotients_zero_left (b : ℕ) :
    euclideanRunQuotients 0 b = [] := by
  rw [euclideanRunQuotients]

private theorem euclideanRunQuotients_zero_right (a : ℕ) :
    euclideanRunQuotients a 0 = [] := by
  cases a <;> rw [euclideanRunQuotients]

private theorem euclideanRunQuotients_of_lt {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    euclideanRunQuotients a b =
      b / a :: euclideanRunQuotients a (b % a) := by
  cases a with
  | zero => omega
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          rw [euclideanRunQuotients]
          split
          · rfl
          · omega

private theorem euclideanRunQuotients_of_not_lt {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : ¬ a < b) :
    euclideanRunQuotients a b =
      a / b :: euclideanRunQuotients (a % b) b := by
  cases a with
  | zero => omega
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          rw [euclideanRunQuotients]
          split
          · omega
          · rfl

private theorem dropInitialRun_length_lt (dir : Bool) (tail : List Bool) :
    (dropInitialRun dir (dir :: tail)).length < (dir :: tail).length := by
  have hk : 0 < initialRunLength dir (dir :: tail) := by
    simp [initialRunLength]
  have hlen :
      (dir :: tail).length =
        initialRunLength dir (dir :: tail) +
          (dropInitialRun dir (dir :: tail)).length := by
    simpa using
      congrArg List.length (initialRun_decomposition dir (dir :: tail))
  omega

private theorem dropInitialRun_eq_nil_or_cons_not (dir : Bool) (path : List Bool) :
    dropInitialRun dir path = [] ∨
      ∃ rest, dropInitialRun dir path = Bool.not dir :: rest := by
  induction path with
  | nil =>
      simp [dropInitialRun]
  | cons b path ih =>
      by_cases h : b = dir
      · subst b
        rw [dropInitialRun]
        simp only [ite_true]
        exact ih
      · right
        have hb : b = Bool.not dir := by
          cases dir <;> cases b <;> simp_all
        refine ⟨path, ?_⟩
        rw [dropInitialRun]
        simp only [h, ite_false]
        rw [hb]

private theorem pair_false_run (k : ℕ) (path : List Bool) :
    pair (List.replicate k false ++ path) =
      ((pair path).1, (pair path).2 + (pair path).1 * k) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [pair]
      rw [ih]
      simp [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm]

private theorem pair_true_run (k : ℕ) (path : List Bool) :
    pair (List.replicate k true ++ path) =
      ((pair path).1 + (pair path).2 * k, (pair path).2) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [pair]
      rw [ih]
      simp [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm]

/-- Quotients read recursively from the canonical maximal runs of a Stern-Brocot path.

Every nonterminal run contributes its length. The final run contributes one extra, matching the
terminal Euclidean quotient convention. The root path has quotient list `[1]`. -/
def pathQuotients : List Bool → List ℕ
  | [] => [1]
  | dir :: tail =>
      let path := dir :: tail
      let k := initialRunLength dir path
      let rest := dropInitialRun dir path
      if rest = [] then [k + 1] else k :: pathQuotients rest
termination_by path => path.length
decreasing_by
  exact dropInitialRun_length_lt dir tail

/-- The complete canonical Stern-Brocot run quotients are exactly the quotients of the symmetric
Euclidean algorithm applied to the represented numerator-denominator pair. -/
theorem euclideanRunQuotients_pair : ∀ path : List Bool,
    euclideanRunQuotients (pair path).1 (pair path).2 = pathQuotients path
  | [] => by
      rw [pair, pathQuotients]
      rw [euclideanRunQuotients_of_not_lt (by omega) (by omega) (by omega)]
      rw [Nat.div_self (by omega), Nat.mod_self, euclideanRunQuotients_zero_left]
  | dir :: tail => by
      let path := dir :: tail
      let k := initialRunLength dir path
      let rest := dropInitialRun dir path
      have hk : 0 < k := by
        simp [k, path, initialRunLength]
      have hrestLen : rest.length < path.length := by
        simpa [rest, path] using dropInitialRun_length_lt dir tail
      have hdecomp : path = List.replicate k dir ++ rest := by
        simpa [path, k, rest] using initialRun_decomposition dir path
      rcases dropInitialRun_eq_nil_or_cons_not dir path with hnil | ⟨u, hcons⟩
      · have hrest : rest = [] := by
          simpa [rest] using hnil
        cases dir
        · have hp : pair path = (1, k + 1) := by
            rw [hdecomp, hrest, pair_false_run]
            simp [pair, Nat.add_comm]
          have hlt : 1 < k + 1 := by omega
          have hq :=
            euclideanRunQuotients_of_lt (a := 1) (b := k + 1)
              (by omega) (by omega) hlt
          rw [hp, hq, Nat.div_one, Nat.mod_one, euclideanRunQuotients_zero_right]
          rw [pathQuotients]
          split
          · rfl
          · rename_i hne
            exact (hne hnil).elim
        · have hp : pair path = (k + 1, 1) := by
            rw [hdecomp, hrest, pair_true_run]
            simp [pair, Nat.add_comm]
          have hnlt : ¬ k + 1 < 1 := by omega
          have hq :=
            euclideanRunQuotients_of_not_lt (a := k + 1) (b := 1)
              (by omega) (by omega) hnlt
          rw [hp, hq, Nat.div_one, Nat.mod_one, euclideanRunQuotients_zero_left]
          rw [pathQuotients]
          split
          · rfl
          · rename_i hne
            exact (hne hnil).elim
      · have hrest : rest = Bool.not dir :: u := by
          simpa [rest] using hcons
        have hrestNe : rest ≠ [] := by
          rw [hrest]
          simp
        have hpos := pair_positive_coprime rest
        have ih := euclideanRunQuotients_pair rest
        cases dir
        · have hsmall : (pair rest).2 < (pair rest).1 := by
            rw [hrest]
            simp only [Bool.not_false, pair]
            have hu := pair_positive_coprime u
            omega
          have hp :
              pair path =
                ((pair rest).1, (pair rest).2 + (pair rest).1 * k) := by
            rw [hdecomp, pair_false_run]
          have hmul : (pair rest).1 ≤ (pair rest).1 * k :=
            Nat.le_mul_of_pos_right _ hk
          have hlt :
              (pair rest).1 <
                (pair rest).2 + (pair rest).1 * k := by
            omega
          have hdiv :
              ((pair rest).2 + (pair rest).1 * k) / (pair rest).1 = k := by
            rw [Nat.add_mul_div_left _ _ hpos.1, Nat.div_eq_of_lt hsmall]
            simp
          have hmod :
              ((pair rest).2 + (pair rest).1 * k) % (pair rest).1 =
                (pair rest).2 := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
          rw [hp]
          rw [euclideanRunQuotients_of_lt hpos.1 (by omega) hlt]
          rw [hdiv, hmod, ih]
          rw [pathQuotients]
          split
          · rename_i heq
            have : rest = [] := by
              simpa [rest, path] using heq
            exact (hrestNe this).elim
          · rfl
        · have hsmall : (pair rest).1 < (pair rest).2 := by
            rw [hrest]
            simp only [Bool.not_true, pair]
            have hu := pair_positive_coprime u
            omega
          have hp :
              pair path =
                ((pair rest).1 + (pair rest).2 * k, (pair rest).2) := by
            rw [hdecomp, pair_true_run]
          have hmul : (pair rest).2 ≤ (pair rest).2 * k :=
            Nat.le_mul_of_pos_right _ hk
          have hnlt :
              ¬ (pair rest).1 + (pair rest).2 * k < (pair rest).2 := by
            omega
          have hdiv :
              ((pair rest).1 + (pair rest).2 * k) / (pair rest).2 = k := by
            rw [Nat.add_mul_div_left _ _ hpos.2.1, Nat.div_eq_of_lt hsmall]
            simp
          have hmod :
              ((pair rest).1 + (pair rest).2 * k) % (pair rest).2 =
                (pair rest).1 := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
          rw [hp]
          rw [euclideanRunQuotients_of_not_lt (by omega) hpos.2.1 hnlt]
          rw [hdiv, hmod, ih]
          rw [pathQuotients]
          split
          · rename_i heq
            have : rest = [] := by
              simpa [rest, path] using heq
            exact (hrestNe this).elim
          · rfl
termination_by path => path.length
decreasing_by
  exact hrestLen

end LeanFrontier.SternBrocot

import LeanFrontier.NumberTheory.SternBrocotEuclidean
import Mathlib.Tactic

/-!
# Canonical initial runs in Stern-Brocot paths

This module packages the first recursive interface between a Stern-Brocot Boolean path and
Euclid's algorithm. For a chosen direction, `initialRunLength` counts the maximal initial
block in that direction and `dropInitialRun` removes it. The path is recovered exactly as
that constant block followed by the remainder.

The main theorem packages one complete Euclidean step: after removing the maximal initial run,
either the path terminates and the corresponding quotient is one larger than the run length, or
the opposite direction begins and the quotient is exactly the run length.

These operations are intended to be iterated by a later run-length / continued-fraction
coefficient interface.
-/

namespace LeanFrontier.SternBrocot

/-- Length of the maximal initial block equal to `dir`. -/
def initialRunLength (dir : Bool) : List Bool → ℕ
  | [] => 0
  | b :: path => if b = dir then initialRunLength dir path + 1 else 0

/-- Remove the maximal initial block equal to `dir`. -/
def dropInitialRun (dir : Bool) : List Bool → List Bool
  | [] => []
  | b :: path => if b = dir then dropInitialRun dir path else b :: path

/-- Every path is its maximal initial `dir`-run followed by the remaining suffix. -/
theorem initialRun_decomposition (dir : Bool) (path : List Bool) :
    path =
      List.replicate (initialRunLength dir path) dir ++ dropInitialRun dir path := by
  induction path with
  | nil =>
      simp [initialRunLength, dropInitialRun]
  | cons b path ih =>
      by_cases h : b = dir
      · subst b
        rw [initialRunLength, dropInitialRun]
        simp only [if_pos rfl]
        rw [List.replicate_succ, List.cons_append, ← ih]
      · simp [initialRunLength, dropInitialRun, h]

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
        simp only [if_pos rfl]
        exact ih
      · right
        have hb : b = Bool.not dir := by
          cases dir <;> cases b <;> simp_all
        refine ⟨path, ?_⟩
        rw [dropInitialRun]
        simp only [if_neg h]
        rw [hb]

/-- The canonical initial run packages one complete Euclidean quotient step.

After splitting off the maximal initial block in direction `dir`, either the path ends and
the quotient is one larger than the run length, or the opposite direction starts and the
quotient is exactly the run length. -/
theorem initialRun_euclidean_step (dir : Bool) (path : List Bool) :
    let k := initialRunLength dir path
    let rest := dropInitialRun dir path
    let p := pair path
    path = List.replicate k dir ++ rest ∧
      ((rest = [] ∧
          (if dir then p.1 / p.2 else p.2 / p.1) = k + 1) ∨
       ∃ tail, rest = Bool.not dir :: tail ∧
          (if dir then p.1 / p.2 else p.2 / p.1) = k) := by
  dsimp only
  constructor
  · exact initialRun_decomposition dir path
  · rcases dropInitialRun_eq_nil_or_cons_not dir path with hnil | ⟨tail, htail⟩
    · left
      refine ⟨hnil, ?_⟩
      have hpath : path = List.replicate (initialRunLength dir path) dir := by
        calc
          path =
              List.replicate (initialRunLength dir path) dir ++
                dropInitialRun dir path :=
            initialRun_decomposition dir path
          _ = List.replicate (initialRunLength dir path) dir := by
            rw [hnil, List.append_nil]
      have hq := terminal_run_euclidean_quotient dir (initialRunLength dir path)
      rw [← hpath] at hq
      exact hq
    · right
      refine ⟨tail, htail, ?_⟩
      have hpath :
          path =
            List.replicate (initialRunLength dir path) dir ++
              (Bool.not dir :: tail) := by
        calc
          path =
              List.replicate (initialRunLength dir path) dir ++
                dropInitialRun dir path :=
            initialRun_decomposition dir path
          _ =
              List.replicate (initialRunLength dir path) dir ++
                (Bool.not dir :: tail) := by
            rw [htail]
      have hq := initial_run_euclidean_quotient dir (initialRunLength dir path) tail
      rw [← hpath] at hq
      exact hq

end LeanFrontier.SternBrocot

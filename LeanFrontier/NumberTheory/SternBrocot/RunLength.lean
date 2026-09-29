import LeanFrontier.NumberTheory.SternBrocotEuclidean
import Mathlib.Tactic

/-!
# Canonical initial runs in Stern-Brocot paths

This module packages the first recursive interface between a Stern-Brocot Boolean path and
Euclid's algorithm.  For a chosen direction, `initialRunLength` counts the maximal initial
block in that direction and `dropInitialRun` removes it.  The path is recovered exactly as
that constant block followed by the remainder.

When the remainder is nonempty, its first direction is necessarily the opposite direction, so
the accepted Stern-Brocot/Euclidean bridge identifies the corresponding Euclidean quotient with
the run length.  When the remainder is empty, the terminal quotient is one larger.

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
        simp [initialRunLength, dropInitialRun, ih, List.replicate_succ]
      · simp [initialRunLength, dropInitialRun, h]

/-- After the maximal initial `dir`-run, either the path ends or the opposite direction begins. -/
theorem dropInitialRun_eq_nil_or_cons_not (dir : Bool) (path : List Bool) :
    dropInitialRun dir path = [] ∨
      ∃ rest, dropInitialRun dir path = Bool.not dir :: rest := by
  induction path with
  | nil =>
      simp [dropInitialRun]
  | cons b path ih =>
      by_cases h : b = dir
      · subst b
        simpa [dropInitialRun] using ih
      · right
        have hb : b = Bool.not dir := by
          cases dir <;> cases b <;> simp_all
        exact ⟨path, by simp [dropInitialRun, h, hb]⟩

/-- A nonterminal canonical initial run has Euclidean quotient equal to its length. -/
theorem initialRunLength_euclidean_quotient
    (dir : Bool) (path rest : List Bool)
    (hrest : dropInitialRun dir path = Bool.not dir :: rest) :
    let p := pair path
    (if dir then p.1 / p.2 else p.2 / p.1) = initialRunLength dir path := by
  have hpath :
      path =
        List.replicate (initialRunLength dir path) dir ++ (Bool.not dir :: rest) := by
    rw [initialRun_decomposition dir path, hrest]
  rw [hpath]
  exact initial_run_euclidean_quotient dir (initialRunLength dir path) rest

/-- A terminal canonical initial run has Euclidean quotient one larger than its length. -/
theorem terminal_initialRunLength_euclidean_quotient
    (dir : Bool) (path : List Bool)
    (hrest : dropInitialRun dir path = []) :
    let p := pair path
    (if dir then p.1 / p.2 else p.2 / p.1) = initialRunLength dir path + 1 := by
  have hpath : path = List.replicate (initialRunLength dir path) dir := by
    simpa [hrest] using initialRun_decomposition dir path
  rw [hpath]
  exact terminal_run_euclidean_quotient dir (initialRunLength dir path)

end LeanFrontier.SternBrocot

import LeanFrontier.NumberTheory.MarkovTree
import Mathlib.Tactic.LinearCombination

/-!
# Paths in the Markov tree

The accepted Markov-equation development supplies the Vieta involution in one
coordinate, and the accepted Markov-tree development supplies the ordered local
descent step.  This module adds the path representation needed to iterate those
moves independently of any ordering convention.

A state bundles the three integer coordinates.  A single parameterized
`Move` chooses which coordinate is replaced by its Vieta companion; this avoids
a family of three permutation copies of the same theorem.  A `walk` is a finite
list of such moves, read from left to right.

The main structural facts are:

* every coordinate move preserves the Markov equation;
* applying the same coordinate move twice returns to the original state;
* every finite walk preserves the Markov equation;
* reversing the move list exactly reverses the walk.

This is deliberately only path infrastructure.  It does not identify different
paths, choose a canonical parent, or assert injectivity of Markov-number labels;
those questions belong to the later Markov/Farey correspondence and must not
cross the Markov uniqueness-conjecture boundary.
-/

namespace LeanFrontier.MarkovTree

/-- A bundled integer state for the three coordinates of the Markov equation. -/
structure State where
  x : ℤ
  y : ℤ
  z : ℤ
deriving DecidableEq

/-- A bundled Markov state satisfies the classical Markov equation. -/
def State.IsSolution (s : State) : Prop :=
  MarkovEquation.IsSolution s.x s.y s.z

/-- Which coordinate of a Markov state is replaced by its Vieta companion. -/
inductive Move
  | first
  | second
  | third
deriving DecidableEq

/-- Apply one coordinate Vieta move to a bundled Markov state. -/
def move : Move → State → State
  | .first, s =>
      ⟨MarkovEquation.jump s.y s.z s.x, s.y, s.z⟩
  | .second, s =>
      ⟨s.x, MarkovEquation.jump s.x s.z s.y, s.z⟩
  | .third, s =>
      ⟨s.x, s.y, MarkovEquation.jump s.x s.y s.z⟩

/-- Every coordinate Vieta move preserves the Markov equation. -/
theorem move_isSolution (m : Move) {s : State} (h : s.IsSolution) :
    (move m s).IsSolution := by
  rcases s with ⟨x, y, z⟩
  cases m <;>
    simp only [State.IsSolution, move] at h ⊢ <;>
    unfold MarkovEquation.IsSolution at h ⊢ <;>
    unfold MarkovEquation.jump <;>
    linear_combination h

/-- Each coordinate Vieta move is an involution. -/
theorem move_involutive (m : Move) (s : State) :
    move m (move m s) = s := by
  rcases s with ⟨x, y, z⟩
  cases m <;> simp [move, MarkovEquation.jump_jump]

/-- Follow a finite list of coordinate Vieta moves from left to right. -/
def walk : List Move → State → State
  | [], s => s
  | m :: path, s => walk path (move m s)

/-- Every finite Markov-tree walk preserves the Markov equation. -/
theorem walk_isSolution (path : List Move) {s : State} (h : s.IsSolution) :
    (walk path s).IsSolution := by
  induction path generalizing s with
  | nil =>
      simpa [walk] using h
  | cons m path ih =>
      simp only [walk]
      exact ih (move_isSolution m h)

private theorem walk_append (left right : List Move) (s : State) :
    walk (left ++ right) s = walk right (walk left s) := by
  induction left generalizing s with
  | nil =>
      rfl
  | cons m left ih =>
      simp only [List.cons_append, walk]
      exact ih (move m s)

/-- Reversing a move list exactly reverses the corresponding Markov-tree walk. -/
theorem walk_reverse (path : List Move) (s : State) :
    walk path.reverse (walk path s) = s := by
  induction path generalizing s with
  | nil =>
      rfl
  | cons m path ih =>
      rw [List.reverse_cons, walk_append]
      simp only [walk]
      rw [ih]
      exact move_involutive m s

end LeanFrontier.MarkovTree

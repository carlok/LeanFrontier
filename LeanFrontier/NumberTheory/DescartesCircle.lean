import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Descartes circle relation

Four mutually tangent circles with curvatures `k₁, k₂, k₃, k₄` satisfy Descartes' relation

`(k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)`,

where a curvature is the reciprocal radius, taken negative for the circle enclosing the other
three. Read as a quadratic in `k₄`, the relation has two roots, so a mutually tangent triple can
be completed to a quadruple in exactly two ways, and passing between them is the reflection
generating an Apollonian gasket.

## Main definitions

* `LeanFrontier.DescartesCircle.IsQuadruple` - Descartes' relation.
* `LeanFrontier.DescartesCircle.reflect` - the second root `2 * (k₁ + k₂ + k₃) - k₄`.

## Main statements

* `LeanFrontier.DescartesCircle.eq_or_eq_reflect` - a mutually tangent triple has exactly two
  completions: any two solutions for the fourth curvature are equal or related by `reflect`.
* `LeanFrontier.DescartesCircle.isQuadruple_reflect` - `reflect` preserves the relation.
* `LeanFrontier.DescartesCircle.reflect_reflect` - `reflect` is an involution.
* `LeanFrontier.DescartesCircle.mul_reflect_eq` - the product of the two roots.
* `LeanFrontier.DescartesCircle.isQuadruple_neg_one_two_two_three` - the quadruple of the
  standard Apollonian gasket.

## Implementation notes

The uniqueness statement `eq_or_eq_reflect` is the reason the other results matter: without it,
`reflect` would only be one way of producing a further solution rather than the only one. It
needs no zero divisors, since it factors the difference of two instances of the relation; the
remaining results hold over an arbitrary commutative ring.

Curvatures are carried as four separate arguments and `reflect` acts on the last. The three
other reflections are this one composed with a permutation of the arguments, so stating them
would restate one result four times.

Nothing here interprets curvature geometrically or derives Descartes' relation from tangency of
actual circles; the relation is taken as the definition of a quadruple, and these are the facts
about that equation.
-/

namespace LeanFrontier.DescartesCircle

variable {R : Type*} [CommRing R] {k₁ k₂ k₃ k₄ x y : R}

/-- Descartes' circle relation for the curvatures of four mutually tangent circles. -/
def IsQuadruple (k₁ k₂ k₃ k₄ : R) : Prop :=
  (k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)

/-- The second solution of Descartes' relation for the fourth curvature, that is the reflection
of `k₄` in the other three. -/
def reflect (k₁ k₂ k₃ k₄ : R) : R := 2 * (k₁ + k₂ + k₃) - k₄

/-- Reflection preserves Descartes' relation. -/
theorem isQuadruple_reflect (h : IsQuadruple k₁ k₂ k₃ k₄) :
    IsQuadruple k₁ k₂ k₃ (reflect k₁ k₂ k₃ k₄) := by
  unfold IsQuadruple at h ⊢
  unfold reflect
  linear_combination h

/-- Reflection is an involution, so the two completions of a mutually tangent triple are
symmetric. -/
theorem reflect_reflect (k₁ k₂ k₃ k₄ : R) :
    reflect k₁ k₂ k₃ (reflect k₁ k₂ k₃ k₄) = k₄ := by
  unfold reflect
  ring

/-- The product of the two solutions for the fourth curvature, the second of Vieta's relations
for Descartes' quadratic. -/
theorem mul_reflect_eq (h : IsQuadruple k₁ k₂ k₃ k₄) :
    k₄ * reflect k₁ k₂ k₃ k₄ = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2 := by
  unfold IsQuadruple at h
  unfold reflect
  linear_combination h

/-- The curvatures `-1, 2, 2, 3` of the standard Apollonian gasket form a quadruple. -/
theorem isQuadruple_neg_one_two_two_three : IsQuadruple (-1 : R) 2 2 3 := by
  unfold IsQuadruple
  norm_num

variable [NoZeroDivisors R]

/-- A mutually tangent triple has exactly two completions: any two fourth curvatures satisfying
Descartes' relation with the same triple are equal, or are each other's reflection. This is what
makes `reflect` the only way to continue an Apollonian gasket. -/
theorem eq_or_eq_reflect (hx : IsQuadruple k₁ k₂ k₃ x) (hy : IsQuadruple k₁ k₂ k₃ y) :
    x = y ∨ x = reflect k₁ k₂ k₃ y := by
  unfold IsQuadruple at hx hy
  unfold reflect
  have hfactor : (x - y) * (x + y - 2 * (k₁ + k₂ + k₃)) = 0 := by linear_combination hy - hx
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact Or.inl (sub_eq_zero.mp hzero)
  · exact Or.inr (by linear_combination hzero)

end LeanFrontier.DescartesCircle

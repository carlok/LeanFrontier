import LeanFrontier.NumberTheory.Mediant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ford circles and the Farey neighbour criterion

The *Ford circle* of a fraction `p / q` is the circle of radius `1 / (2 * q ^ 2)` centred at
`(p / q, 1 / (2 * q ^ 2))`, so it is tangent to the horizontal axis at `p / q`. Ford's
observation is that two such circles touch exactly when their fractions are Farey neighbours,
that is when the cross determinant `q * r - p * s` of the two numerator/denominator pairs is
`1` or `-1`, and that they never overlap.

This module proves that criterion in the form of an exact difference: the squared distance
between two centres minus the squared sum of the two radii equals
`(crossDet p q r s ^ 2 - 1) / (q ^ 2 * s ^ 2)`. Tangency and non-overlap both follow by reading
off the sign of that one expression.

## Main definitions

* `LeanFrontier.FordCircle.radius` - the radius `1 / (2 * q ^ 2)` of the Ford circle of `p / q`,
  which is also the height of its centre.
* `LeanFrontier.FordCircle.centerDistSq` - the squared distance between two Ford circle centres.

## Main statements

* `LeanFrontier.FordCircle.centerDistSq_sub_sq_radius_add` - the exact difference formula.
* `LeanFrontier.FordCircle.centerDistSq_eq_iff` - the centres are exactly the sum of the radii
  apart precisely when the cross determinant squares to `1`.
* `LeanFrontier.FordCircle.sq_radius_add_le_centerDistSq` - over an ordered field, two Ford
  circles whose cross determinant is at least `1` in absolute value never overlap.

## Implementation notes

Everything is stated over an arbitrary field in which `2` is invertible, which is exactly what
the radius `1 / (2 * q ^ 2)` needs; an order is assumed only for the non-overlap inequality.
The cross determinant is `LeanFrontier.Mediant.crossDet`, reused rather than restated, which is
what ties this criterion to the Stern-Brocot construction where that determinant is the
invariant.

Distances appear squared throughout, which keeps the statements free of square roots and valid
over any field. Over an ordered field the squared form is equivalent to the unsquared one, since
both distance and the sum of two radii are nonnegative.

A bridge to `EuclideanGeometry.Sphere.IsExtTangent` is not included, and not merely as a matter
of taste: that predicate is existential over a point of tangency, through
`EuclideanGeometry.Sphere.IsExtTangentAt`, so connecting to it requires exhibiting that point
and is separate work rather than a restatement of what is proved here.
-/

namespace LeanFrontier.FordCircle

variable {K : Type*} [Field K] [NeZero (2 : K)] {p q r s : K}

/-- The radius `1 / (2 * q ^ 2)` of the Ford circle of the fraction `p / q`. It is also the
height of the circle's centre, so the circle is tangent to the horizontal axis. -/
def radius (q : K) : K := 1 / (2 * q ^ 2)

/-- The squared distance between the centres of the Ford circles of `p / q` and `r / s`. -/
def centerDistSq (p q r s : K) : K := (p / q - r / s) ^ 2 + (radius q - radius s) ^ 2

/-- The exact defect of the tangency relation between two Ford circles: the squared distance
between the centres, minus the squared sum of the radii, is governed entirely by the cross
determinant of the two numerator/denominator pairs. -/
theorem centerDistSq_sub_sq_radius_add (hq : q ≠ 0) (hs : s ≠ 0) :
    centerDistSq p q r s - (radius q + radius s) ^ 2
      = (Mediant.crossDet p q r s ^ 2 - 1) / (q ^ 2 * s ^ 2) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  unfold centerDistSq radius Mediant.crossDet
  field_simp
  ring

/-- Two Ford circles have centres exactly the sum of their radii apart precisely when their
fractions are Farey neighbours, that is when the cross determinant is `1` or `-1`. -/
theorem centerDistSq_eq_iff (hq : q ≠ 0) (hs : s ≠ 0) :
    centerDistSq p q r s = (radius q + radius s) ^ 2 ↔ Mediant.crossDet p q r s ^ 2 = 1 := by
  have hqs : q ^ 2 * s ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hs)
  rw [← sub_eq_zero, centerDistSq_sub_sq_radius_add hq hs, div_eq_zero_iff]
  simp [hqs, sub_eq_zero]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Ford circles never overlap: once the cross determinant is at least `1` in absolute value,
the centres are at least the sum of the radii apart. -/
theorem sq_radius_add_le_centerDistSq (hq : q ≠ 0) (hs : s ≠ 0)
    (h : 1 ≤ Mediant.crossDet p q r s ^ 2) :
    (radius q + radius s) ^ 2 ≤ centerDistSq p q r s := by
  have hqs : 0 < q ^ 2 * s ^ 2 := by positivity
  have hdefect : 0 ≤ centerDistSq p q r s - (radius q + radius s) ^ 2 := by
    rw [centerDistSq_sub_sq_radius_add hq hs]
    exact div_nonneg (by linarith) hqs.le
  linarith

end LeanFrontier.FordCircle

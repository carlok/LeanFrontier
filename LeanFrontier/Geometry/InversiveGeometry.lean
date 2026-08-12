import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Reflection across a generalized circle

A *generalized circle* (or *circline*) in the extended complex plane is a circle or a line,
treated as a single kind of object. Such a set is the zero locus of a Hermitian form

`H z = A * (z * conj z) + B * z + conj B * conj z + C`

with `A, C : ℝ` and `B : ℂ`. The form is self-conjugate, so `H z = 0` is a single real
equation; the case `A = 0` cuts out a line and `A ≠ 0` a circle of centre `-conj B / A`.

This module defines the associated reflection and proves the two facts that characterize it:
its fixed points are exactly the zero locus, and it is an involution.

## Main definitions

* `LeanFrontier.InversiveGeometry.hermitianForm` - the Hermitian form whose zero locus is the
  generalized circle.
* `LeanFrontier.InversiveGeometry.reflect` - reflection across that circle.

## Main statements

* `LeanFrontier.InversiveGeometry.reflect_eq_self_iff` - the fixed points of the reflection are
  the zero locus of the Hermitian form.
* `LeanFrontier.InversiveGeometry.reflect_reflect` - the reflection is an involution.

## Implementation notes

`reflect` is obtained by solving `H z = 0` for `z` in terms of `conj z`, so the fixed-point
characterization holds by construction. Being a Möbius transformation precomposed with
conjugation, it is anti-holomorphic, which is the orientation-reversing behaviour a reflection
should have.

The generalized circle is not bundled as a structure. These statements are about `ℂ` with real
and complex coefficients, so they survive any later choice of representation.

Division by a zero denominator returns `0` under Lean's field convention, so `reflect` is total
but only meaningful away from its pole. That pole is the centre of the circle, where inversion
genuinely has no value. Both theorems therefore carry explicit non-vanishing-denominator
hypotheses rather than restricting the domain.
-/

open ComplexConjugate

namespace LeanFrontier.InversiveGeometry

variable (A C : ℝ) (B : ℂ)

/-- The Hermitian form `A|z|² + Bz + conj B * conj z + C` whose zero locus is a generalized
circle, for real `A`, `C` and complex `B`. -/
noncomputable def hermitianForm (z : ℂ) : ℂ :=
  (A : ℂ) * (z * conj z) + B * z + conj B * conj z + (C : ℂ)

/-- Reflection across the generalized circle cut out by `hermitianForm A C B`.

This is the anti-Möbius involution obtained by solving `hermitianForm A C B z = 0` for `z` in
terms of `conj z`. -/
noncomputable def reflect (z : ℂ) : ℂ :=
  (-conj B * conj z - (C : ℂ)) / ((A : ℂ) * conj z + B)

/-- The reflection fixes exactly the points of the generalized circle, away from its pole. -/
theorem reflect_eq_self_iff (z : ℂ) (hden : (A : ℂ) * conj z + B ≠ 0) :
    reflect A C B z = z ↔ hermitianForm A C B z = 0 := by
  unfold reflect hermitianForm
  rw [div_eq_iff hden]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- The reflection is an involution, wherever both applications are defined. -/
theorem reflect_reflect (z : ℂ) (hden1 : (A : ℂ) * conj z + B ≠ 0)
    (hden2 : (A : ℂ) * conj (reflect A C B z) + B ≠ 0) :
    reflect A C B (reflect A C B z) = z := by
  have hconjne : ∀ x : ℂ, conj x = 0 → x = 0 := fun x hx => by
    have := congrArg conj hx
    simpa [Complex.conj_conj] using this
  have hAB : (A : ℂ) * z + conj B = conj ((A : ℂ) * conj z + B) := by
    simp [map_add, map_mul]
  have hden1' : (A : ℂ) * z + conj B ≠ 0 := by
    rw [hAB]; exact fun h => hden1 (hconjne _ h)
  have hconjw : conj (reflect A C B z) = (-B * z - (C : ℂ)) / ((A : ℂ) * z + conj B) := by
    unfold reflect
    rw [map_div₀]
    congr 1
    · simp [map_sub, map_neg, map_mul]
    · simp [map_add, map_mul]
  have hkey : conj (reflect A C B z) * ((A : ℂ) * z + conj B) = -B * z - (C : ℂ) := by
    rw [hconjw, div_mul_cancel₀ _ hden1']
  set w := reflect A C B z with hw_def
  unfold reflect
  rw [div_eq_iff hden2]
  linear_combination -hkey

end LeanFrontier.InversiveGeometry

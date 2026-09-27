import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Hornich-Hlawka inequality

The Hornich-Hlawka inequality is a classical inequality for real inner-product spaces:

```
‖x + y‖ + ‖y + z‖ + ‖z + x‖
  ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖.
```

The proof used here is the standard algebraic proof.  The parallelogram-type identity

```
‖x + y + z‖² + ‖x‖² + ‖y‖² + ‖z‖²
  = ‖x + y‖² + ‖y + z‖² + ‖z + x‖²
```

turns the desired difference, after multiplication by the sum of the four norms on the
right-hand side, into a sum of three products.  Every factor in those products is nonnegative
by the triangle inequality.
-/

namespace LeanFrontier.InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hornich_hlawka_sq_identity (x y z : E) :
    ‖x + y + z‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 =
      ‖x + y‖ ^ 2 + ‖y + z‖ ^ 2 + ‖z + x‖ ^ 2 := by
  simp only [norm_add_sq_real, inner_add_left]
  rw [real_inner_comm z x]
  ring

omit [InnerProductSpace ℝ E] in
private theorem norm_pair_le_total_add_other (x y z : E) :
    ‖x + y‖ ≤ ‖x + y + z‖ + ‖z‖ := by
  calc
    ‖x + y‖ = ‖(x + y + z) - z‖ := by
      congr 1
      abel
    _ ≤ ‖x + y + z‖ + ‖z‖ := norm_sub_le _ _

/-- **Hornich-Hlawka inequality.** In a real inner-product space, the sum of the norms of the
three pairwise sums is bounded by the sum of the three individual norms and the norm of the
total sum. -/
theorem hornich_hlawka (x y z : E) :
    ‖x + y‖ + ‖y + z‖ + ‖z + x‖ ≤
      ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ := by
  have hsq := hornich_hlawka_sq_identity x y z

  have hxy₁ : 0 ≤ ‖x‖ + ‖y‖ - ‖x + y‖ :=
    sub_nonneg.mpr (norm_add_le x y)
  have hyz₁ : 0 ≤ ‖y‖ + ‖z‖ - ‖y + z‖ :=
    sub_nonneg.mpr (norm_add_le y z)
  have hzx₁ : 0 ≤ ‖z‖ + ‖x‖ - ‖z + x‖ :=
    sub_nonneg.mpr (norm_add_le z x)

  have hxy₂ : 0 ≤ ‖x + y + z‖ + ‖z‖ - ‖x + y‖ :=
    sub_nonneg.mpr (norm_pair_le_total_add_other x y z)
  have hyz₂ : 0 ≤ ‖x + y + z‖ + ‖x‖ - ‖y + z‖ := by
    apply sub_nonneg.mpr
    have h := norm_pair_le_total_add_other y z x
    simpa only [add_assoc, add_comm, add_left_comm] using h
  have hzx₂ : 0 ≤ ‖x + y + z‖ + ‖y‖ - ‖z + x‖ := by
    apply sub_nonneg.mpr
    have h := norm_pair_le_total_add_other z x y
    simpa only [add_assoc, add_comm, add_left_comm] using h

  have hp₁ :
      0 ≤ (‖x‖ + ‖y‖ - ‖x + y‖) *
        (‖x + y + z‖ + ‖z‖ - ‖x + y‖) :=
    mul_nonneg hxy₁ hxy₂
  have hp₂ :
      0 ≤ (‖y‖ + ‖z‖ - ‖y + z‖) *
        (‖x + y + z‖ + ‖x‖ - ‖y + z‖) :=
    mul_nonneg hyz₁ hyz₂
  have hp₃ :
      0 ≤ (‖z‖ + ‖x‖ - ‖z + x‖) *
        (‖x + y + z‖ + ‖y‖ - ‖z + x‖) :=
    mul_nonneg hzx₁ hzx₂

  let R : ℝ := ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖
  let D : ℝ :=
    R - (‖x + y‖ + ‖y + z‖ + ‖z + x‖)

  have hDR : 0 ≤ D * R := by
    dsimp [D, R]
    nlinarith

  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity

  by_cases hRzero : R = 0
  · have hxnorm : ‖x‖ = 0 := by
      dsimp [R] at hRzero
      nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg z, norm_nonneg (x + y + z)]
    have hynorm : ‖y‖ = 0 := by
      dsimp [R] at hRzero
      nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg z, norm_nonneg (x + y + z)]
    have hznorm : ‖z‖ = 0 := by
      dsimp [R] at hRzero
      nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg z, norm_nonneg (x + y + z)]
    have hx : x = 0 := norm_eq_zero.mp hxnorm
    have hy : y = 0 := norm_eq_zero.mp hynorm
    have hz : z = 0 := norm_eq_zero.mp hznorm
    simp [hx, hy, hz]
  · have hRpos : 0 < R :=
      lt_of_le_of_ne hRnonneg (Ne.symm hRzero)
    have hD : 0 ≤ D := by
      by_contra h
      have hDneg : D < 0 := lt_of_not_ge h
      have : D * R < 0 := mul_neg_of_neg_of_pos hDneg hRpos
      linarith
    dsimp [D, R] at hD
    linarith

end LeanFrontier.InnerProductGeometry

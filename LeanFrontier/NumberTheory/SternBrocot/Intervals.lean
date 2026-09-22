import LeanFrontier.NumberTheory.Mediant

/-!
# Stern-Brocot interval invariants

The Stern-Brocot construction starts from the bounding fractions `0/1` and `1/0`.
At each left step the right boundary is replaced by the mediant, and at each right step the
left boundary is replaced by the mediant.

This module records that interval state directly. Its main invariant is unimodularity: the
cross determinant of the two boundary pairs remains `1` along every finite path. Consequently
the mediant of every such interval is in lowest terms. The denominator sum is also always
positive, including along the two infinite-side spines where one boundary denominator remains
zero.

This is independent of any particular enumeration order and is intended to connect the
accepted mediant/Farey theory to explicit Stern-Brocot path representations.
-/

namespace LeanFrontier.SternBrocot

private def leftStep
    (state : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let left := state.1
  let right := state.2
  (left, (left.1 + right.1, left.2 + right.2))

private def rightStep
    (state : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let left := state.1
  let right := state.2
  ((left.1 + right.1, left.2 + right.2), right)

private def boundsRev : List Bool → (ℤ × ℤ) × (ℤ × ℤ)
  | [] => ((0, 1), (1, 0))
  | false :: path => leftStep (boundsRev path)
  | true :: path => rightStep (boundsRev path)

/-- The ordered boundary pairs of the Stern-Brocot interval reached by a root-to-leaf Boolean
path. The result is `((a,b),(c,d))`, representing the left boundary `a/b` and right boundary
`c/d`. -/
def bounds (path : List Bool) : (ℤ × ℤ) × (ℤ × ℤ) :=
  boundsRev path.reverse

/-- Appending one root-to-leaf edge updates exactly one boundary by the mediant of the current
boundaries: `false` replaces the right boundary and `true` replaces the left boundary. -/
theorem bounds_append (path : List Bool) (dir : Bool) :
    bounds (path ++ [dir]) =
      if dir then
        (((bounds path).1.1 + (bounds path).2.1,
            (bounds path).1.2 + (bounds path).2.2), (bounds path).2)
      else
        ((bounds path).1,
          ((bounds path).1.1 + (bounds path).2.1,
            (bounds path).1.2 + (bounds path).2.2)) := by
  unfold bounds
  rw [List.reverse_append]
  cases dir <;> simp [boundsRev, leftStep, rightStep]

private def det (state : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ :=
  Mediant.crossDet state.1.1 state.1.2 state.2.1 state.2.2

private theorem det_leftStep (state : (ℤ × ℤ) × (ℤ × ℤ)) :
    det (leftStep state) = det state := by
  rcases state with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simpa [det, leftStep] using Mediant.crossDet_left_mediant a b c d

private theorem det_rightStep (state : (ℤ × ℤ) × (ℤ × ℤ)) :
    det (rightStep state) = det state := by
  rcases state with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simpa [det, rightStep] using Mediant.crossDet_mediant_right a b c d

private theorem det_boundsRev (path : List Bool) : det (boundsRev path) = 1 := by
  induction path with
  | nil =>
      simp [det, boundsRev, Mediant.crossDet]
  | cons dir path ih =>
      cases dir
      · simp only [boundsRev, det_leftStep, ih]
      · simp only [boundsRev, det_rightStep, ih]

private def DenGood (state : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  0 ≤ state.1.2 ∧ 0 ≤ state.2.2 ∧ 0 < state.1.2 + state.2.2

private theorem denGood_leftStep (state : (ℤ × ℤ) × (ℤ × ℤ))
    (h : DenGood state) : DenGood (leftStep state) := by
  rcases state with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [DenGood, leftStep, Prod.fst, Prod.snd] at h ⊢
  rcases h with ⟨hb, hd, hsum⟩
  exact ⟨hb, by linarith, by linarith⟩

private theorem denGood_rightStep (state : (ℤ × ℤ) × (ℤ × ℤ))
    (h : DenGood state) : DenGood (rightStep state) := by
  rcases state with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [DenGood, rightStep, Prod.fst, Prod.snd] at h ⊢
  rcases h with ⟨hb, hd, hsum⟩
  exact ⟨by linarith, hd, by linarith⟩

private theorem denGood_boundsRev (path : List Bool) : DenGood (boundsRev path) := by
  induction path with
  | nil =>
      simp [DenGood, boundsRev]
  | cons dir path ih =>
      cases dir
      · exact denGood_leftStep (boundsRev path) ih
      · exact denGood_rightStep (boundsRev path) ih

/-- The two boundary pairs of every Stern-Brocot interval are unimodular: their cross
determinant is exactly `1`. -/
theorem crossDet_bounds (path : List Bool) :
    Mediant.crossDet
      (bounds path).1.1 (bounds path).1.2
      (bounds path).2.1 (bounds path).2.2 = 1 := by
  simpa [bounds, det] using det_boundsRev path.reverse

/-- The denominator of the mediant of every Stern-Brocot interval is positive. This includes
the outer spines where one of the two boundary denominators is still zero. -/
theorem mediantDen_pos (path : List Bool) :
    0 < (bounds path).1.2 + (bounds path).2.2 := by
  unfold bounds
  exact (denGood_boundsRev path.reverse).2.2

/-- The mediant numerator and denominator of every Stern-Brocot interval are coprime. Thus every
node produced by the interval construction is already a reduced fraction. -/
theorem mediant_isCoprime (path : List Bool) :
    IsCoprime
      ((bounds path).1.1 + (bounds path).2.1)
      ((bounds path).1.2 + (bounds path).2.2) := by
  apply Mediant.isCoprime_mediant
  exact crossDet_bounds path

end LeanFrontier.SternBrocot

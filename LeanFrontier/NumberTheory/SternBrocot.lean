import LeanFrontier.NumberTheory.SternDiatomic.Enumeration

/-!
# Root-to-leaf paths in the Stern-Brocot tree

The Stern-Brocot tree can be described directly on numerator-denominator pairs. The root is
`(1,1)`. A left edge applies `(a,b) ↦ (a,a+b)`, while a right edge applies
`(a,b) ↦ (a+b,b)` to the subtree that follows it.

The direction order matters. For a root-to-leaf path `L,R`, one first enters the left
subtree and then takes its right branch, obtaining `2/3`. This is the path convention needed
for a later comparison with the Calkin-Wilf indexing, whose binary path is read in the opposite
direction.

The main theorem proves the classical path form of the Stern-Brocot enumeration: every positive
coprime numerator-denominator pair occurs at exactly one finite Boolean path.
-/

namespace LeanFrontier.SternBrocot

/-- The numerator-denominator pair reached by a root-to-leaf Stern-Brocot path. `false` is a
left edge and `true` is a right edge. -/
def pair : List Bool → ℕ × ℕ
  | [] => (1, 1)
  | false :: path =>
      let p := pair path
      (p.1, p.1 + p.2)
  | true :: path =>
      let p := pair path
      (p.1 + p.2, p.2)

/-- Every Stern-Brocot path reaches a pair of positive coprime naturals. -/
theorem pair_positive_coprime (path : List Bool) :
    0 < (pair path).1 ∧ 0 < (pair path).2 ∧ Nat.Coprime (pair path).1 (pair path).2 := by
  induction path with
  | nil =>
      simp [pair]
  | cons dir path ih =>
      rcases ih with ⟨hfirst, hsecond, hcop⟩
      cases dir
      · simp only [pair]
        refine ⟨hfirst, by omega, ?_⟩
        exact Nat.coprime_self_add_right.mpr hcop
      · simp only [pair]
        refine ⟨by omega, hsecond, ?_⟩
        exact Nat.coprime_add_self_left.mpr hcop

private theorem existsUnique_pair_aux :
    ∀ s a b : ℕ, a + b ≤ s → 0 < a → 0 < b → Nat.Coprime a b →
      ∃! path : List Bool, pair path = (a, b) := by
  intro s
  induction s with
  | zero =>
      intro a b hsum ha hb _
      omega
  | succ s ih =>
      intro a b hsum ha hb hab
      rcases lt_trichotomy a b with hablt | habeq | habgt
      · have hsplit : b = a + (b - a) := by omega
        have hcop : Nat.Coprime a (b - a) := by
          rw [hsplit] at hab
          exact Nat.coprime_self_add_right.mp hab
        obtain ⟨path, hpath, huniq⟩ :=
          ih a (b - a) (by omega) ha (by omega) hcop
        refine ⟨false :: path, ?_, ?_⟩
        · simp only [pair]
          rw [hpath]
          apply Prod.ext <;> simp <;> omega
        · intro other hother
          cases other with
          | nil =>
              simp [pair] at hother
              omega
          | cons dir rest =>
              cases dir
              · simp only [pair] at hother
                injection hother with hfirst hsecond
                have hrest : pair rest = (a, b - a) := by
                  apply Prod.ext
                  · exact hfirst
                  · omega
                have hrestEq : rest = path := huniq rest hrest
                simp [hrestEq]
              · simp only [pair] at hother
                injection hother with hfirst hsecond
                have hrestPos := (pair_positive_coprime rest).2.1
                omega
      · have hgcd : Nat.gcd a b = 1 := hab
        rw [← habeq, Nat.gcd_self] at hgcd
        have ha1 : a = 1 := by omega
        have hb1 : b = 1 := by omega
        subst a
        subst b
        refine ⟨[], by simp [pair], ?_⟩
        intro other hother
        cases other with
        | nil =>
            rfl
        | cons dir rest =>
            cases dir
            · simp only [pair] at hother
              injection hother with hfirst hsecond
              have hrestPos := (pair_positive_coprime rest).2.1
              omega
            · simp only [pair] at hother
              injection hother with hfirst hsecond
              have hrestPos := (pair_positive_coprime rest).1
              omega
      · have hsplit : a = a - b + b := by omega
        have hcop : Nat.Coprime (a - b) b := by
          rw [hsplit] at hab
          exact Nat.coprime_add_self_left.mp hab
        obtain ⟨path, hpath, huniq⟩ :=
          ih (a - b) b (by omega) (by omega) hb hcop
        refine ⟨true :: path, ?_, ?_⟩
        · simp only [pair]
          rw [hpath]
          apply Prod.ext <;> simp <;> omega
        · intro other hother
          cases other with
          | nil =>
              simp [pair] at hother
              omega
          | cons dir rest =>
              cases dir
              · simp only [pair] at hother
                injection hother with hfirst hsecond
                have hrestPos := (pair_positive_coprime rest).1
                omega
              · simp only [pair] at hother
                injection hother with hfirst hsecond
                have hrest : pair rest = (a - b, b) := by
                  apply Prod.ext
                  · omega
                  · exact hsecond
                have hrestEq : rest = path := huniq rest hrest
                simp [hrestEq]

/-- Every positive coprime numerator-denominator pair occurs at exactly one root-to-leaf path
in the Stern-Brocot tree. -/
theorem existsUnique_pair_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    ∃! path : List Bool, pair path = (a, b) :=
  existsUnique_pair_aux (a + b) a b le_rfl ha hb hab

end LeanFrontier.SternBrocot

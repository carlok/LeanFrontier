import LeanFrontier.NumberTheory.SternDiatomic.Enumeration

/-!
# Paths in the Calkin-Wilf tree

The accepted Stern-diatomic enumeration shows that the consecutive pair
`(fusc n, fusc (n + 1))` runs exactly once through the positive coprime pairs.
This module upgrades that arithmetic enumeration to an explicit binary-tree path interface.

A path is a list of booleans in root-to-leaf order. A left step sends `(a,b)` to
`(a,a+b)`; a right step sends it to `(a+b,b)`. Starting from `(1,1)`, these are the
Calkin-Wilf child operations. The associated binary code starts at `1` and appends `0`
for a left edge and `1` for a right edge.

The main theorem says that every positive coprime pair is reached by exactly one such path.
This supplies reusable tree/path infrastructure for the later comparison with Stern-Brocot
mediant paths; it does not identify the two tree orders.
-/

namespace LeanFrontier.CalkinWilf

private def pairRev : List Bool → ℕ × ℕ
  | [] => (1, 1)
  | false :: path =>
      let p := pairRev path
      (p.1, p.1 + p.2)
  | true :: path =>
      let p := pairRev path
      (p.1 + p.2, p.2)

private def codeRev : List Bool → ℕ
  | [] => 1
  | false :: path => 2 * codeRev path
  | true :: path => 2 * codeRev path + 1

/-- The positive-integer binary code of a root-to-leaf Calkin-Wilf path. The root has code
`1`; a left edge appends a binary `0`, and a right edge appends a binary `1`. -/
def code (path : List Bool) : ℕ := codeRev path.reverse

/-- The numerator-denominator pair reached by a root-to-leaf path in the Calkin-Wilf tree,
starting at `(1,1)`. -/
def pair (path : List Bool) : ℕ × ℕ := pairRev path.reverse

private theorem codeRev_pos (path : List Bool) : 0 < codeRev path := by
  induction path with
  | nil =>
      simp [codeRev]
  | cons b path ih =>
      cases b <;> simp [codeRev] <;> omega

/-- Every Calkin-Wilf path has a positive binary code. -/
theorem code_pos (path : List Bool) : 0 < code path := by
  unfold code
  exact codeRev_pos path.reverse

/-- Appending one root-to-leaf edge applies the corresponding Calkin-Wilf child operation to
the pair already reached: `false` keeps the numerator and adds it to the denominator, while
`true` keeps the denominator and adds it to the numerator. -/
theorem pair_append (path : List Bool) (dir : Bool) :
    pair (path ++ [dir]) =
      if dir then ((pair path).1 + (pair path).2, (pair path).2)
      else ((pair path).1, (pair path).1 + (pair path).2) := by
  unfold pair
  rw [List.reverse_append]
  cases dir <;> simp [pairRev]

private theorem fusc_pair_codeRev (path : List Bool) :
    SternDiatomic.fusc (codeRev path) = (pairRev path).1 ∧
      SternDiatomic.fusc (codeRev path + 1) = (pairRev path).2 := by
  induction path with
  | nil =>
      simp [codeRev, pairRev, SternDiatomic.fusc]
  | cons b path ih =>
      cases b
      · simp only [codeRev, pairRev]
        constructor
        · rw [SternDiatomic.fusc_two_mul, ih.1]
        · rw [SternDiatomic.fusc_two_mul_add_one, ih.1, ih.2]
      · simp only [codeRev, pairRev]
        constructor
        · rw [SternDiatomic.fusc_two_mul_add_one, ih.1, ih.2]
        · have hsucc : 2 * codeRev path + 1 + 1 = 2 * (codeRev path + 1) := by omega
          rw [hsucc, SternDiatomic.fusc_two_mul, ih.2]

/-- The pair reached by a path is exactly the consecutive Stern-diatomic pair at its binary
code. This is the bridge between the path representation and the accepted arithmetic
enumeration. -/
theorem fusc_pair_code (path : List Bool) :
    SternDiatomic.fusc (code path) = (pair path).1 ∧
      SternDiatomic.fusc (code path + 1) = (pair path).2 := by
  exact fusc_pair_codeRev path.reverse

private theorem codeRev_eq_iff (p q : List Bool) : codeRev p = codeRev q ↔ p = q := by
  constructor
  · revert q
    induction p with
    | nil =>
        intro q h
        cases q with
        | nil => rfl
        | cons b q =>
            have hpos := codeRev_pos q
            cases b <;> simp [codeRev] at h <;> omega
    | cons b p ih =>
        intro q h
        cases q with
        | nil =>
            have hpos := codeRev_pos p
            cases b <;> simp [codeRev] at h <;> omega
        | cons c q =>
            cases b <;> cases c
            · simp only [codeRev] at h
              have hpq : codeRev p = codeRev q := by omega
              have := ih q hpq
              simp [this]
            · simp only [codeRev] at h
              omega
            · simp only [codeRev] at h
              omega
            · simp only [codeRev] at h
              have hpq : codeRev p = codeRev q := by omega
              have := ih q hpq
              simp [this]
  · rintro rfl
    rfl

/-- Two root-to-leaf paths have the same binary code exactly when they are the same path. -/
theorem code_eq_iff (p q : List Bool) : code p = code q ↔ p = q := by
  unfold code
  constructor
  · intro h
    have hrev : p.reverse = q.reverse := (codeRev_eq_iff p.reverse q.reverse).mp h
    simpa using congrArg List.reverse hrev
  · rintro rfl
    rfl

private theorem exists_codeRev_eq {n : ℕ} (hn : 0 < n) : ∃ path : List Bool, codeRev path = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        exact ⟨[], rfl⟩
      · rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
        · have hkpos : 0 < k := by omega
          obtain ⟨path, hpath⟩ := ih k (by omega) hkpos
          refine ⟨false :: path, ?_⟩
          simp [codeRev, hpath, hk]
        · have hkpos : 0 < k := by omega
          obtain ⟨path, hpath⟩ := ih k (by omega) hkpos
          refine ⟨true :: path, ?_⟩
          simp [codeRev, hpath, hk]

/-- Every positive natural number is the binary code of a unique-rooted Calkin-Wilf path. -/
theorem exists_code_eq {n : ℕ} (hn : 0 < n) : ∃ path : List Bool, code path = n := by
  obtain ⟨path, hpath⟩ := exists_codeRev_eq hn
  refine ⟨path.reverse, ?_⟩
  simpa [code] using hpath

/-- Two root-to-leaf paths reach the same Calkin-Wilf pair exactly when they are the same
path. This uses the accepted theorem that a positive index is determined by its consecutive
Stern-diatomic pair. -/
theorem pair_eq_iff (p q : List Bool) : pair p = pair q ↔ p = q := by
  constructor
  · intro hpq
    have hp := fusc_pair_code p
    have hq := fusc_pair_code q
    have hcode : code p = code q := by
      apply SternDiatomic.eq_of_fusc_pair_eq (code_pos p) (code_pos q)
      · calc
          SternDiatomic.fusc (code p) = (pair p).1 := hp.1
          _ = (pair q).1 := congrArg Prod.fst hpq
          _ = SternDiatomic.fusc (code q) := hq.1.symm
      · calc
          SternDiatomic.fusc (code p + 1) = (pair p).2 := hp.2
          _ = (pair q).2 := congrArg Prod.snd hpq
          _ = SternDiatomic.fusc (code q + 1) := hq.2.symm
    exact (code_eq_iff p q).mp hcode
  · rintro rfl
    rfl

/-- Every Calkin-Wilf path reaches a pair of positive coprime naturals. -/
theorem pair_positive_coprime (path : List Bool) :
    0 < (pair path).1 ∧ 0 < (pair path).2 ∧ Nat.Coprime (pair path).1 (pair path).2 := by
  have hp := fusc_pair_code path
  have hcpos := code_pos path
  refine ⟨?_, ?_, ?_⟩
  · rw [← hp.1]
    exact SternDiatomic.fusc_pos (by omega)
  · rw [← hp.2]
    exact SternDiatomic.fusc_pos (by omega)
  · rw [← hp.1, ← hp.2]
    exact SternDiatomic.coprime_fusc_fusc_succ (code path)

/-- Every positive coprime numerator-denominator pair occurs at exactly one root-to-leaf
Calkin-Wilf path. This is the path-level form of the accepted Stern-diatomic enumeration. -/
theorem existsUnique_pair_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    ∃! path : List Bool, pair path = (a, b) := by
  obtain ⟨n, hn, hfuscA, hfuscB⟩ :=
    SternDiatomic.exists_fusc_eq_of_coprime ha hb hab
  obtain ⟨path, hcode⟩ := exists_code_eq hn
  have hp := fusc_pair_code path
  have hpair : pair path = (a, b) := by
    apply Prod.ext
    · calc
        (pair path).1 = SternDiatomic.fusc (code path) := hp.1.symm
        _ = SternDiatomic.fusc n := by rw [hcode]
        _ = a := hfuscA
    · calc
        (pair path).2 = SternDiatomic.fusc (code path + 1) := hp.2.symm
        _ = SternDiatomic.fusc (n + 1) := by rw [hcode]
        _ = b := hfuscB
  refine ⟨path, hpair, ?_⟩
  intro other hother
  exact (pair_eq_iff other path).mp (hother.trans hpair.symm)

end LeanFrontier.CalkinWilf

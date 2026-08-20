import LeanFrontier.NumberTheory.SternDiatomic
import Mathlib.Algebra.Ring.Parity

/-!
# The Stern-Brocot enumeration of the coprime pairs

`LeanFrontier.NumberTheory.SternDiatomic` defines Stern's diatomic sequence `fusc` and proves
that consecutive values are coprime and positive, so that `fusc n / fusc (n + 1)` is always a
positive rational in lowest terms. That leaves open the statement those two facts exist to
support: that the pairs `(fusc n, fusc (n + 1))` for `n ≠ 0` run through *every* coprime pair
of positive naturals, and each of them exactly once.

This module proves it, in both directions:

* surjectivity, `exists_fusc_eq_of_coprime`, by strong induction on `a + b`: the subtractive
  Euclidean step `(a, b) ↦ (a, b - a)` or `(a - b, b)` is undone by the halving equations
  `fusc (2 * n) = fusc n` and `fusc (2 * n + 1) = fusc n + fusc (n + 1)`, which say precisely
  that the pair at `2 * n` is `(a, a + b)` and the pair at `2 * n + 1` is `(a + b, b)` when the
  pair at `n` is `(a, b)`;
* injectivity, `eq_of_fusc_pair_eq`, by strong induction on the index, using that the parity of
  `n` is legible from the pair: at an even index the pair increases and at an odd index it
  decreases, and the two coincide only at `n = 1`.

Combining them, `existsUnique_fusc_eq_of_coprime` states the enumeration.

## Main statements

* `LeanFrontier.SternDiatomic.existsUnique_fusc_eq_of_coprime` - every coprime pair of positive
  naturals is `(fusc n, fusc (n + 1))` for exactly one `n`.
* `LeanFrontier.SternDiatomic.exists_fusc_eq_of_coprime` - the existence half.
* `LeanFrontier.SternDiatomic.eq_of_fusc_pair_eq` - the uniqueness half.
* `LeanFrontier.SternDiatomic.fusc_eq_fusc_succ_iff` - a value equals its successor exactly at
  index `1`, the fixed point at the root of the tree.
* `LeanFrontier.SternDiatomic.fusc_surjective` - every natural number is a value of `fusc`.

## Implementation notes

Nothing here inspects the definition of `fusc`; the two halving equations and positivity from
the accepted module are the whole interface, which is why the same argument would transfer to
any sequence satisfying them.

The descent in the existence proof is on `a + b` rather than on the pair, so it is an ordinary
induction on a natural number bound. The `a = b` case is where coprimality does its work: it
forces `a = b = 1`, the root of the tree, and is the base case.

The comparison lemmas that drive injectivity are `private`: they are statements about the
indices `2 * k` and `2 * k + 1` rather than about a general index, and their only public
consequence is `fusc_eq_fusc_succ_iff`.
-/

namespace LeanFrontier.SternDiatomic

private theorem fusc_one : fusc 1 = 1 := by simp [fusc]

private theorem fusc_two : fusc 2 = 1 := by
  have h : fusc (2 * 1) = fusc 1 := fusc_two_mul 1
  simpa [fusc_one] using h

/-- At an even positive index the sequence strictly increases. -/
private theorem fusc_lt_fusc_succ {k : ℕ} (hk : 0 < k) : fusc (2 * k) < fusc (2 * k + 1) := by
  rw [fusc_two_mul, fusc_two_mul_add_one]
  have h := fusc_pos (n := k + 1) (by omega)
  omega

/-- At an odd index above `1` the sequence strictly decreases. -/
private theorem fusc_succ_lt_fusc {k : ℕ} (hk : 0 < k) :
    fusc (2 * k + 1 + 1) < fusc (2 * k + 1) := by
  have hsucc : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  rw [hsucc, fusc_two_mul, fusc_two_mul_add_one]
  have h := fusc_pos (n := k) (by omega)
  omega

/-- A value of Stern's diatomic sequence equals the next one exactly at index `1`, where the
pair is `(1, 1)`. Everywhere else the pair is strictly monotone in a direction that records the
parity of the index, which is what makes the enumeration injective. -/
theorem fusc_eq_fusc_succ_iff {n : ℕ} (hn : 0 < n) : fusc n = fusc (n + 1) ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · subst hk
      have := fusc_lt_fusc_succ (k := k) (by omega)
      omega
    · subst hk
      have := fusc_succ_lt_fusc (k := k) (by omega)
      omega
  · rintro rfl
    have h1 : fusc 1 = 1 := fusc_one
    have h2 : fusc (1 + 1) = 1 := by simpa using fusc_two
    omega

private theorem exists_index_aux : ∀ s a b : ℕ, a + b ≤ s → 0 < a → 0 < b → Nat.Coprime a b →
    ∃ n, 0 < n ∧ fusc n = a ∧ fusc (n + 1) = b := by
  intro s
  induction s with
  | zero =>
    intro a b hs ha hb _
    omega
  | succ s ih =>
    intro a b hs ha hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hsplit : b = a + (b - a) := by omega
      have hcop : Nat.Coprime a (b - a) := by
        rw [hsplit] at hab
        exact Nat.coprime_self_add_right.mp hab
      obtain ⟨n, hn, h1, h2⟩ := ih a (b - a) (by omega) ha (by omega) hcop
      refine ⟨2 * n, by omega, ?_, ?_⟩
      · rw [fusc_two_mul, h1]
      · rw [fusc_two_mul_add_one, h1, h2]
        omega
    · have hgcd : Nat.gcd a b = 1 := hab
      rw [← heq, Nat.gcd_self] at hgcd
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [fusc_one]
        omega
      · have h2 : fusc (1 + 1) = 1 := by simpa using fusc_two
        omega
    · have hsplit : a = a - b + b := by omega
      have hcop : Nat.Coprime (a - b) b := by
        rw [hsplit] at hab
        exact Nat.coprime_add_self_left.mp hab
      obtain ⟨n, hn, h1, h2⟩ := ih (a - b) b (by omega) (by omega) hb hcop
      refine ⟨2 * n + 1, by omega, ?_, ?_⟩
      · rw [fusc_two_mul_add_one, h1, h2]
        omega
      · have hsucc : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
        rw [hsucc, fusc_two_mul, h2]

/-- Every pair of coprime positive naturals occurs as a pair of consecutive values of Stern's
diatomic sequence. Together with `LeanFrontier.SternDiatomic.coprime_fusc_fusc_succ` this says
that the fractions `fusc n / fusc (n + 1)` are exactly the positive rationals in lowest
terms. -/
theorem exists_fusc_eq_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ n, 0 < n ∧ fusc n = a ∧ fusc (n + 1) = b :=
  exists_index_aux (a + b) a b le_rfl ha hb hab

private theorem eq_of_fusc_pair_eq_aux : ∀ m n : ℕ, 0 < m → 0 < n →
    fusc m = fusc n → fusc (m + 1) = fusc (n + 1) → m = n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm hn h₀ h₁
    by_cases hm1 : m = 1
    · have hfixm : fusc m = fusc (m + 1) := (fusc_eq_fusc_succ_iff hm).mpr hm1
      have hfixn : fusc n = fusc (n + 1) := by
        rw [← h₀, ← h₁]
        exact hfixm
      have hn1 : n = 1 := (fusc_eq_fusc_succ_iff hn).mp hfixn
      omega
    · by_cases hn1 : n = 1
      · have hfixn : fusc n = fusc (n + 1) := (fusc_eq_fusc_succ_iff hn).mpr hn1
        have hfixm : fusc m = fusc (m + 1) := by
          rw [h₀, h₁]
          exact hfixn
        exact absurd ((fusc_eq_fusc_succ_iff hm).mp hfixm) hm1
      · rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
        · rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
          · subst hj
            subst hk
            rw [fusc_two_mul, fusc_two_mul] at h₀
            rw [fusc_two_mul_add_one, fusc_two_mul_add_one] at h₁
            have hsucc : fusc (j + 1) = fusc (k + 1) := by omega
            have := ih j (by omega) k (by omega) (by omega) h₀ hsucc
            omega
          · subst hj
            subst hk
            have hlt := fusc_lt_fusc_succ (k := j) (by omega)
            have hgt := fusc_succ_lt_fusc (k := k) (by omega)
            omega
        · rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
          · subst hj
            subst hk
            have hgt := fusc_succ_lt_fusc (k := j) (by omega)
            have hlt := fusc_lt_fusc_succ (k := k) (by omega)
            omega
          · subst hj
            subst hk
            have hsj : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
            have hsk : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
            rw [hsj, hsk, fusc_two_mul, fusc_two_mul] at h₁
            rw [fusc_two_mul_add_one, fusc_two_mul_add_one] at h₀
            have hjk : fusc j = fusc k := by omega
            have := ih j (by omega) k (by omega) (by omega) hjk h₁
            omega

/-- An index above `0` is determined by its pair of consecutive values: the map
`n ↦ (fusc n, fusc (n + 1))` is injective on the positive naturals. -/
theorem eq_of_fusc_pair_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h₀ : fusc m = fusc n)
    (h₁ : fusc (m + 1) = fusc (n + 1)) : m = n :=
  eq_of_fusc_pair_eq_aux m n hm hn h₀ h₁

/-- The Stern-Brocot enumeration: the consecutive pairs of Stern's diatomic sequence run
through every pair of coprime positive naturals exactly once. -/
theorem existsUnique_fusc_eq_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) : ∃! n : ℕ, 0 < n ∧ fusc n = a ∧ fusc (n + 1) = b := by
  obtain ⟨n, hn, h1, h2⟩ := exists_fusc_eq_of_coprime ha hb hab
  refine ⟨n, ⟨hn, h1, h2⟩, ?_⟩
  rintro m ⟨hm, hm1, hm2⟩
  exact eq_of_fusc_pair_eq hm hn (by rw [hm1, h1]) (by rw [hm2, h2])

/-- Stern's diatomic sequence is surjective: every natural number occurs as a value, since
`(a, 1)` is a coprime pair for every positive `a`. -/
theorem fusc_surjective : Function.Surjective fusc := by
  intro a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, by simp [fusc]⟩
  · obtain ⟨n, -, h1, -⟩ :=
      exists_fusc_eq_of_coprime ha Nat.one_pos (Nat.coprime_one_right a)
    exact ⟨n, h1⟩

end LeanFrontier.SternDiatomic

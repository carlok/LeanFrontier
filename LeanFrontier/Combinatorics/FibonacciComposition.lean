import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Fib.Basic

/-!
# Compositions into parts one and two are counted by Fibonacci numbers

A composition of `n` into parts `1` and `2` is an ordered list of ones and twos summing to
`n`; equivalently, a tiling of a `1 × n` strip by squares and dominoes. The classical
enumerative fact is that there are exactly `fib (n + 1)` of them: `1, 1, 2, 3, 5, ...` for
`n = 0, 1, 2, 3, 4, ...`. This is the standard combinatorial interpretation of the Fibonacci
sequence.

## Main definitions

* `LeanFrontier.Nat.oneTwoCompositions` - the finite set of compositions of `n` with all
  parts equal to `1` or `2`, built by recursion on the first part.

## Main statements

* `LeanFrontier.Nat.mem_oneTwoCompositions` - the defining recursion enumerates exactly the
  lists of ones and twos summing to `n`, so the recursive set matches the a priori
  description.
* `LeanFrontier.Nat.card_oneTwoCompositions` - the count is `fib (n + 1)`.
* `LeanFrontier.Nat.length_le_of_mem_oneTwoCompositions` and
  `LeanFrontier.Nat.le_two_mul_length_of_mem_oneTwoCompositions` - a composition of `n` into
  ones and twos has between `n / 2` (in the sense `n ≤ 2 * length`) and `n` parts.
* `LeanFrontier.Nat.reverse_mem_oneTwoCompositions` - the set is closed under reversal.

## Implementation notes

The set is defined by structural two-step recursion on `n`: a composition of `n + 2` starts
with `1` followed by a composition of `n + 1`, or with `2` followed by a composition of `n`.
The two branches are `Finset.image` under list cons, which is injective, and they are
disjoint because the first parts differ; this makes the cardinality recursion exactly the
Fibonacci recursion, and `card_oneTwoCompositions` is proved with no double counting
argument beyond that disjointness.

`mem_oneTwoCompositions` is the bridge between the recursive definition and the
non-recursive description as `l.sum = n` with parts in `{1, 2}`; it is proved by induction
on the list. All remaining statements are consequences of that characterization and never
unfold the definition again.
-/

namespace LeanFrontier.Nat

open List

/-- The compositions of `n` with every part equal to `1` or `2`, as a finite set of lists:
tilings of a `1 × n` strip by squares and dominoes, recorded left to right. A composition of
`n + 2` begins with a `1` followed by a composition of `n + 1`, or with a `2` followed by a
composition of `n`. -/
def oneTwoCompositions : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => {[1]}
  | n + 2 =>
    ((oneTwoCompositions (n + 1)).image (1 :: ·)) ∪ ((oneTwoCompositions n).image (2 :: ·))

@[simp] theorem oneTwoCompositions_zero : oneTwoCompositions 0 = {[]} := rfl

@[simp] theorem oneTwoCompositions_one : oneTwoCompositions 1 = {[1]} := rfl

theorem oneTwoCompositions_add_two (n : ℕ) :
    oneTwoCompositions (n + 2) =
      ((oneTwoCompositions (n + 1)).image (1 :: ·))
        ∪ ((oneTwoCompositions n).image (2 :: ·)) := rfl

/-- A list of ones and twos with sum zero is empty. -/
private theorem eq_nil_of_sum_eq_zero {l : List ℕ} (hmem : ∀ x ∈ l, x = 1 ∨ x = 2)
    (hsum : l.sum = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t =>
    have ha := hmem a mem_cons_self
    have := sum_cons (a := a) (l := t)
    omega

/-- Membership in `oneTwoCompositions n` is exactly the a priori description: the list sums
to `n` and every part is `1` or `2`. -/
theorem mem_oneTwoCompositions {n : ℕ} {l : List ℕ} :
    l ∈ oneTwoCompositions n ↔ l.sum = n ∧ ∀ x ∈ l, x = 1 ∨ x = 2 := by
  induction l generalizing n with
  | nil =>
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 => simp [oneTwoCompositions_add_two]
  | cons a t ih =>
    match n with
    | 0 =>
      simp only [oneTwoCompositions_zero, Finset.mem_singleton, sum_cons, mem_cons]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨hsum, hmem⟩
        have := hmem a (Or.inl rfl)
        omega
    | 1 =>
      simp only [oneTwoCompositions_one, Finset.mem_singleton, sum_cons, mem_cons]
      constructor
      · rintro h
        obtain ⟨rfl, rfl⟩ : a = 1 ∧ t = [] := by simpa using h
        simp
      · rintro ⟨hsum, hmem⟩
        have ha := hmem a (Or.inl rfl)
        have ha1 : a = 1 := by omega
        have ht : t = [] :=
          eq_nil_of_sum_eq_zero (fun x hx => hmem x (Or.inr hx)) (by omega)
        simp [ha1, ht]
    | n + 2 =>
      simp only [oneTwoCompositions_add_two, Finset.mem_union, Finset.mem_image,
        cons.injEq, sum_cons, mem_cons]
      constructor
      · rintro (⟨s, hs, rfl, rfl⟩ | ⟨s, hs, rfl, rfl⟩)
        · obtain ⟨hsum, hmem⟩ := ih.mp hs
          refine ⟨by omega, ?_⟩
          rintro x (rfl | hx)
          · exact Or.inl rfl
          · exact hmem x hx
        · obtain ⟨hsum, hmem⟩ := ih.mp hs
          refine ⟨by omega, ?_⟩
          rintro x (rfl | hx)
          · exact Or.inr rfl
          · exact hmem x hx
      · rintro ⟨hsum, hmem⟩
        have ht : ∀ x ∈ t, x = 1 ∨ x = 2 := fun x hx => hmem x (Or.inr hx)
        rcases hmem a (Or.inl rfl) with rfl | rfl
        · exact Or.inl ⟨t, ih.mpr ⟨by omega, ht⟩, rfl, rfl⟩
        · exact Or.inr ⟨t, ih.mpr ⟨by omega, ht⟩, rfl, rfl⟩

/-- The compositions of `n` into parts `1` and `2` are counted by the Fibonacci numbers:
there are `fib (n + 1)` of them. -/
theorem card_oneTwoCompositions : ∀ n, (oneTwoCompositions n).card = Nat.fib (n + 1)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have ih1 := card_oneTwoCompositions n
    have ih2 := card_oneTwoCompositions (n + 1)
    have hdisj :
        Disjoint ((oneTwoCompositions (n + 1)).image (1 :: ·))
          ((oneTwoCompositions n).image (2 :: ·)) := by
      rw [Finset.disjoint_left]
      rintro l hl1 hl2
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hl1
      obtain ⟨u, -, h⟩ := Finset.mem_image.mp hl2
      exact absurd (head_eq_of_cons_eq h) (by omega)
    rw [oneTwoCompositions_add_two, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (cons_injective),
      Finset.card_image_of_injective _ (cons_injective), ih1, ih2,
      Nat.fib_add_two (n := n + 1)]
    omega

private theorem length_le_sum_of_forall_one_le :
    ∀ {l : List ℕ}, (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum
  | [], _ => by simp
  | a :: t, h => by
    have ha := h a mem_cons_self
    have ht := length_le_sum_of_forall_one_le fun x hx => h x (mem_cons_of_mem a hx)
    simp only [length_cons, sum_cons]
    omega

private theorem sum_le_two_mul_length_of_forall_le_two :
    ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ 2) → l.sum ≤ 2 * l.length
  | [], _ => by simp
  | a :: t, h => by
    have ha := h a mem_cons_self
    have ht := sum_le_two_mul_length_of_forall_le_two fun x hx => h x (mem_cons_of_mem a hx)
    simp only [length_cons, sum_cons]
    omega

/-- A composition of `n` into parts `1` and `2` has at most `n` parts. -/
theorem length_le_of_mem_oneTwoCompositions {n : ℕ} {l : List ℕ}
    (h : l ∈ oneTwoCompositions n) : l.length ≤ n := by
  obtain ⟨rfl, hmem⟩ := mem_oneTwoCompositions.mp h
  exact length_le_sum_of_forall_one_le fun x hx => by
    rcases hmem x hx with rfl | rfl <;> omega

/-- A composition of `n` into parts `1` and `2` has at least `n / 2` parts, in the
subtraction-free form `n ≤ 2 * length`. -/
theorem le_two_mul_length_of_mem_oneTwoCompositions {n : ℕ} {l : List ℕ}
    (h : l ∈ oneTwoCompositions n) : n ≤ 2 * l.length := by
  obtain ⟨rfl, hmem⟩ := mem_oneTwoCompositions.mp h
  exact sum_le_two_mul_length_of_forall_le_two fun x hx => by
    rcases hmem x hx with rfl | rfl <;> omega

/-- Reading a composition of `n` into parts `1` and `2` right to left gives another one:
the set is closed under list reversal. -/
theorem reverse_mem_oneTwoCompositions {n : ℕ} {l : List ℕ}
    (h : l ∈ oneTwoCompositions n) : l.reverse ∈ oneTwoCompositions n := by
  obtain ⟨hsum, hmem⟩ := mem_oneTwoCompositions.mp h
  exact mem_oneTwoCompositions.mpr
    ⟨by simpa using hsum, fun x hx => hmem x (mem_reverse.mp hx)⟩

/-- The five compositions of `4`: `1+1+1+1`, `1+1+2`, `1+2+1`, `2+1+1`, `2+2`. -/
example : (oneTwoCompositions 4).card = 5 := by decide

end LeanFrontier.Nat

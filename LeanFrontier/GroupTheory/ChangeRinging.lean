import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Change ringing: Stedman's plain changes

English tower bells swing full circle and are too heavy to be rung to a melody: a ringer
can only hold a bell back or push it on far enough to exchange it with a neighbour in the
striking order. What is rung is therefore a sequence of *rows* - orderings of the bells -
in which consecutive rows differ by swapping bells in adjacent positions. An *extent*
rings every possible row exactly once. Ringers have rung extents since the seventeenth
century, and Fabian Stedman's *Campanalogia* (1677) describes the *plain changes*, which
visit all `n!` rows swapping a single adjacent pair at each step. Three centuries later
the same ordering was rediscovered as the Steinhaus-Johnson-Trotter enumeration of
permutations.

This file constructs the plain changes and proves the extent properties: starting from a
given row, the list `rows l` has `(length l)!` entries, contains every permutation of `l`
exactly once, begins with `l` itself, and consecutive entries differ by one adjacent
transposition. The construction reuses `List.permutations'Aux`, which inserts the new bell
into every position of a row; the new bell hunts down through one row and back up through
the next, and this alternation is what makes consecutive blocks join correctly.

## Main definitions

* `LeanFrontier.ChangeRinging.AdjSwap` - two rows differ by one swap of adjacent places.
* `LeanFrontier.ChangeRinging.hunt` - one block: the new bell hunts through a fixed row.
* `LeanFrontier.ChangeRinging.rows` - the plain changes on a given start row.

## Main results

* `LeanFrontier.ChangeRinging.length_rows` - the extent has `(length l)!` rows.
* `LeanFrontier.ChangeRinging.mem_rows` - a row is rung iff it is a permutation of `l`.
* `LeanFrontier.ChangeRinging.nodup_rows` - no row is rung twice.
* `LeanFrontier.ChangeRinging.isChain_adjSwap_rows` - consecutive rows differ by a single
  adjacent transposition.
* `LeanFrontier.ChangeRinging.head_rows` - the ringing starts from the given row.
-/

namespace LeanFrontier.ChangeRinging

open List

variable {α : Type*}

/-- Two rows differ by a *change* in the ringers' sense restricted to one pair: some two
adjacent places swap their bells and every other bell stays put. -/
def AdjSwap (l₁ l₂ : List α) : Prop :=
  ∃ p q x y, l₁ = p ++ x :: y :: q ∧ l₂ = p ++ y :: x :: q

theorem adjSwap_symm {l₁ l₂ : List α} (h : AdjSwap l₁ l₂) : AdjSwap l₂ l₁ := by
  obtain ⟨p, q, x, y, h₁, h₂⟩ := h
  exact ⟨p, q, y, x, h₂, h₁⟩

theorem adjSwap_cons (z : α) {l₁ l₂ : List α} (h : AdjSwap l₁ l₂) :
    AdjSwap (z :: l₁) (z :: l₂) := by
  obtain ⟨p, q, x, y, rfl, rfl⟩ := h
  exact ⟨z :: p, q, x, y, rfl, rfl⟩

theorem adjSwap_concat (z : α) {l₁ l₂ : List α} (h : AdjSwap l₁ l₂) :
    AdjSwap (l₁ ++ [z]) (l₂ ++ [z]) := by
  obtain ⟨p, q, x, y, rfl, rfl⟩ := h
  exact ⟨p, q ++ [z], x, y, by simp, by simp⟩

/-- A single change permutes the bells: no bell appears or disappears. -/
theorem adjSwap_perm {l₁ l₂ : List α} (h : AdjSwap l₁ l₂) : l₁ ~ l₂ := by
  obtain ⟨p, q, x, y, rfl, rfl⟩ := h
  exact Perm.append_left p (Perm.swap y x q)

theorem permutations'Aux_ne_nil (a : α) (r : List α) : permutations'Aux a r ≠ [] := by
  cases r <;> simp [permutations'Aux]

theorem head?_permutations'Aux (a : α) (r : List α) :
    (permutations'Aux a r).head? = some (a :: r) := by
  cases r <;> rfl

theorem getLast?_permutations'Aux (a : α) (r : List α) :
    (permutations'Aux a r).getLast? = some (r ++ [a]) := by
  induction r with
  | nil => rfl
  | cons y ys ih =>
    have hne : (permutations'Aux a ys).map (cons y) ≠ [] := by
      simp [permutations'Aux_ne_nil]
    obtain ⟨z, zs, hz⟩ := exists_cons_of_ne_nil hne
    rw [show permutations'Aux a (y :: ys)
          = (a :: y :: ys) :: (permutations'Aux a ys).map (cons y) from rfl,
      hz, getLast?_cons_cons, ← hz, getLast?_map, ih, Option.map_some, cons_append]

/-- Successive insertions of the hunting bell differ by carrying it past one resident
bell, which is a single change. -/
theorem isChain_adjSwap_permutations'Aux (a : α) (r : List α) :
    IsChain AdjSwap (permutations'Aux a r) := by
  induction r with
  | nil => exact .singleton _
  | cons y ys ih =>
    simp only [permutations'Aux]
    refine IsChain.cons (isChain_map_of_isChain _ (fun s t h => adjSwap_cons y h) ih) ?_
    intro z hz
    rw [head?_map, head?_permutations'Aux, Option.map_some] at hz
    obtain rfl : y :: a :: ys = z := by simpa using hz
    exact ⟨[], ys, a, y, rfl, rfl⟩

/-- One block of the plain changes: the new bell `a` hunts through the row `r`, entering
at the front when `b` is `true` and at the back when `b` is `false`. -/
def hunt (a : α) (b : Bool) (r : List α) : List (List α) :=
  if b then permutations'Aux a r else (permutations'Aux a r).reverse

@[simp]
theorem hunt_true (a : α) (r : List α) : hunt a true r = permutations'Aux a r := rfl

@[simp]
theorem hunt_false (a : α) (r : List α) :
    hunt a false r = (permutations'Aux a r).reverse := rfl

theorem getLast?_hunt_true (a : α) (r : List α) :
    (hunt a true r).getLast? = some (r ++ [a]) := by
  rw [hunt_true, getLast?_permutations'Aux]

theorem getLast?_hunt_false (a : α) (r : List α) :
    (hunt a false r).getLast? = some (a :: r) := by
  rw [hunt_false, getLast?_reverse, head?_permutations'Aux]

theorem isChain_adjSwap_hunt (a : α) (b : Bool) (r : List α) :
    IsChain AdjSwap (hunt a b r) := by
  cases b
  · rw [hunt_false, isChain_reverse]
    exact (isChain_adjSwap_permutations'Aux a r).imp fun _ _ h => adjSwap_symm h
  · rw [hunt_true]
    exact isChain_adjSwap_permutations'Aux a r

/-- The new bell hunts through every row of the shorter extent in turn, reversing
direction at each row. The alternation makes consecutive blocks join by a single
change. -/
def weave (a : α) : Bool → List (List α) → List (List α)
  | _, [] => []
  | b, r :: rs => hunt a b r ++ weave a (!b) rs

@[simp]
theorem weave_nil (a : α) (b : Bool) : weave a b [] = [] := rfl

theorem weave_cons (a : α) (b : Bool) (r : List α) (rs : List (List α)) :
    weave a b (r :: rs) = hunt a b r ++ weave a (!b) rs := rfl

theorem head?_weave_true (a : α) (r : List α) (rs : List (List α)) :
    (weave a true (r :: rs)).head? = some (a :: r) := by
  rw [weave_cons, head?_append, hunt_true, head?_permutations'Aux, Option.some_or]

theorem head?_weave_false (a : α) (r : List α) (rs : List (List α)) :
    (weave a false (r :: rs)).head? = some (r ++ [a]) := by
  rw [weave_cons, head?_append, hunt_false, head?_reverse, getLast?_permutations'Aux,
    Option.some_or]

/-- If consecutive rows of the shorter extent differ by a single change, so do
consecutive rows of the weave: within a block the hunting bell moves one place, and at a
junction the underlying change happens behind a stationary hunting bell. -/
theorem isChain_adjSwap_weave (a : α) (b : Bool) (rs : List (List α))
    (h : IsChain AdjSwap rs) : IsChain AdjSwap (weave a b rs) := by
  induction rs generalizing b with
  | nil => exact .nil
  | cons r rs ih =>
    rw [weave_cons]
    refine (isChain_adjSwap_hunt a b r).append (ih (!b) h.tail) ?_
    intro x hx y hy
    cases rs with
    | nil => simp at hy
    | cons r' rs' =>
      have hrr' : AdjSwap r r' := (isChain_cons_cons.mp h).1
      cases b
      · rw [getLast?_hunt_false] at hx
        rw [Bool.not_false, head?_weave_true] at hy
        obtain rfl : a :: r = x := by simpa using hx
        obtain rfl : a :: r' = y := by simpa using hy
        exact adjSwap_cons a hrr'
      · rw [getLast?_hunt_true] at hx
        rw [Bool.not_true, head?_weave_false] at hy
        obtain rfl : r ++ [a] = x := by simpa using hx
        obtain rfl : r' ++ [a] = y := by simpa using hy
        exact adjSwap_concat a hrr'

/-- The plain changes on the start row `l`: strip off the first bell, ring the plain
changes on the rest, and let the first bell hunt through them. -/
def rows : List α → List (List α)
  | [] => [[]]
  | a :: l => weave a true (rows l)

@[simp]
theorem rows_nil : rows ([] : List α) = [[]] := rfl

theorem rows_cons (a : α) (l : List α) : rows (a :: l) = weave a true (rows l) := rfl

/-- Reversing blocks does not change their content, so the weave is a rearrangement of
inserting the new bell everywhere in every row. -/
theorem weave_perm_flatMap (a : α) (b : Bool) (rs : List (List α)) :
    weave a b rs ~ rs.flatMap (permutations'Aux a) := by
  induction rs generalizing b with
  | nil => exact Perm.refl _
  | cons r rs ih =>
    rw [weave_cons, flatMap_cons]
    refine Perm.append ?_ (ih (!b))
    cases b
    · rw [hunt_false]
      exact reverse_perm _
    · rw [hunt_true]

theorem rows_perm_permutations' (l : List α) : rows l ~ permutations' l := by
  induction l with
  | nil => exact Perm.refl _
  | cons a l ih =>
    rw [rows_cons]
    exact (weave_perm_flatMap a true (rows l)).trans (ih.flatMap_right _)

/-- The extent property, first part: the plain changes ring `(length l)!` rows. -/
theorem length_rows (l : List α) : (rows l).length = Nat.factorial l.length := by
  rw [(rows_perm_permutations' l).length_eq, ← (permutations_perm_permutations' l).length_eq,
    length_permutations]

/-- The extent property, second part: a row is rung exactly when it is an ordering of
the bells of the start row. -/
theorem mem_rows {s l : List α} : s ∈ rows l ↔ s ~ l :=
  ((rows_perm_permutations' l).mem_iff).trans mem_permutations'

/-- The extent property, third part: when the bells are distinct, no row is rung
twice. -/
theorem nodup_rows {l : List α} (hl : l.Nodup) : (rows l).Nodup := by
  rw [(rows_perm_permutations' l).nodup_iff, ← (permutations_perm_permutations' l).nodup_iff]
  exact nodup_permutations l hl

/-- The extent property, fourth part: consecutive rows differ by a single change of two
adjacent bells. This is the statement that the plain changes can actually be rung. -/
theorem isChain_adjSwap_rows (l : List α) : IsChain AdjSwap (rows l) := by
  induction l with
  | nil => exact .singleton _
  | cons a l ih => exact isChain_adjSwap_weave a true (rows l) ih

/-- The ringing starts from the given row. -/
theorem head_rows (l : List α) : (rows l).head? = some l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨rs, hrs⟩ : ∃ rs, rows l = l :: rs := by
      cases h : rows l with
      | nil => rw [h] at ih; simp at ih
      | cons r rs =>
        rw [h, head?_cons, Option.some_inj] at ih
        exact ⟨rs, by rw [ih]⟩
    rw [rows_cons, hrs, head?_weave_true]

end LeanFrontier.ChangeRinging

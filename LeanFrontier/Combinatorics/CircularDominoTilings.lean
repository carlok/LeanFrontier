import LeanFrontier.Combinatorics.FibonacciComposition
import LeanFrontier.NumberTheory.LucasNumber

/-!
# Circular square-and-domino tilings are counted by Lucas numbers

The accepted `oneTwoCompositions n` are square-and-domino tilings of a labelled strip of
length `n`, counted by `fib (n + 1)`. Cutting a labelled circle at one distinguished
boundary gives two disjoint cases:

* no domino crosses the cut, leaving an ordinary strip tiling of all `n` cells;
* one domino crosses the cut, covering the two cells adjacent to it and leaving an ordinary
  strip tiling of the remaining `n - 2` cells.

We encode the two cases by a boolean tag. For circumferences at least two this gives
`F (n + 1) + F (n - 1) = L n`, providing a direct combinatorial bridge from the accepted
Fibonacci-composition development to the accepted Lucas-number development.
-/

namespace LeanFrontier.Nat

/-- Labelled circular tilings by squares and dominoes, represented relative to a distinguished
cut. The boolean records whether a domino crosses that cut; in the crossing case the list
records the strip tiling of the remaining `n - 2` cells.

For `n < 2` the crossing case is suppressed. The Lucas counting theorem below is stated for
`n + 2`, where the geometric decomposition is nondegenerate. -/
def circularOneTwoTilings (n : ℕ) : Finset (Bool × List ℕ) :=
  ((oneTwoCompositions n).image (fun l => (false, l))) ∪
    if 2 ≤ n then
      (oneTwoCompositions (n - 2)).image (fun l => (true, l))
    else
      ∅

/-- For a circle of `n + 2` labelled cells, membership splits exactly into the no-crossing
strip tilings of all cells and the crossing tilings of the remaining `n` cells. -/
theorem mem_circularOneTwoTilings_add_two {n : ℕ} {crosses : Bool} {l : List ℕ} :
    (crosses, l) ∈ circularOneTwoTilings (n + 2) ↔
      (crosses = false ∧ l ∈ oneTwoCompositions (n + 2)) ∨
      (crosses = true ∧ l ∈ oneTwoCompositions n) := by
  cases crosses <;> simp [circularOneTwoTilings]

/-- Circular square-and-domino tilings of `n + 2` labelled cells are counted by the Lucas
number `L (n + 2)`. The two tagged cases contribute `F (n + 3)` and `F (n + 1)`
respectively. -/
theorem card_circularOneTwoTilings_add_two (n : ℕ) :
    (circularOneTwoTilings (n + 2)).card = lucas (n + 2) := by
  have htwo : 2 ≤ n + 2 := by omega
  have hsub : n + 2 - 2 = n := by omega
  have hdisj :
      Disjoint
        ((oneTwoCompositions (n + 2)).image (fun l => (false, l)))
        ((oneTwoCompositions n).image (fun l => (true, l))) := by
    rw [Finset.disjoint_left]
    intro x hxFalse hxTrue
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hxFalse
    obtain ⟨r, -, h⟩ := Finset.mem_image.mp hxTrue
    simp at h
  rw [circularOneTwoTilings, if_pos htwo, hsub,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (by
      intro a b h
      exact congrArg Prod.snd h),
    Finset.card_image_of_injective _ (by
      intro a b h
      exact congrArg Prod.snd h),
    card_oneTwoCompositions, card_oneTwoCompositions,
    lucas_succ_eq_fib_add_fib (n + 1)]
  have hidx : n + 2 + 1 = n + 1 + 2 := by omega
  rw [hidx]
  exact Nat.add_comm _ _

end LeanFrontier.Nat

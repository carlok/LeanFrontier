import LeanFrontier.NumberTheory.MarkovTree.SternBrocot
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# The Fibonacci spine of the oriented Markov tree

The accepted oriented Markov/Stern-Brocot bridge gives a canonical binary branch rooted at
`(1,1,2)`.  The constant-right path in that tree is the classical Fibonacci branch of the
Markov tree.

The sequence used here is

`markovFib n = F_(2n+1)`,

the odd-index Fibonacci numbers viewed as integers.  Consecutive terms satisfy exactly the
Vieta recurrence `a_(n+2) = 3 a_(n+1) - a_n`.

Along the all-`true` Stern-Brocot path, the first coordinate stays equal to `1`.  The other
two coordinates are consecutive terms of `markovFib`; their order alternates because the
distinguished back edge alternates between the second and third coordinate moves.  The two main
theorems below give exact formulas at even and odd depths.

This is a branch-identification theorem at the accepted tree-position level.  It does not make
any injectivity claim about Markov numbers.
-/

namespace LeanFrontier.MarkovTree

/-- The odd-index Fibonacci sequence `F_(2n+1)`, viewed in `ℤ`.  These are the
nontrivial coordinates on the classical Fibonacci branch of the Markov tree. -/
def markovFib (n : ℕ) : ℤ :=
  (Nat.fib (2 * n + 1) : ℤ)

/-- Consecutive odd-index Fibonacci numbers satisfy the same second-order recurrence as
successive Vieta jumps along the Markov branch. -/
theorem markovFib_vieta_recurrence (n : ℕ) :
    markovFib (n + 2) = 3 * markovFib (n + 1) - markovFib n := by
  have h0 := Nat.fib_add_two (n := 2 * n + 1)
  rw [show 2 * n + 1 + 2 = 2 * n + 3 by omega] at h0
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega] at h0
  have h1 := Nat.fib_add_two (n := 2 * n + 2)
  rw [show 2 * n + 2 + 2 = 2 * n + 4 by omega] at h1
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by omega] at h1
  have h2 := Nat.fib_add_two (n := 2 * n + 3)
  rw [show 2 * n + 3 + 2 = 2 * n + 5 by omega] at h2
  rw [show 2 * n + 3 + 1 = 2 * n + 4 by omega] at h2
  have hNat :
      Nat.fib (2 * n + 5) + Nat.fib (2 * n + 1) =
        3 * Nat.fib (2 * n + 3) := by
    omega
  have hInt :
      (Nat.fib (2 * n + 5) : ℤ) + (Nat.fib (2 * n + 1) : ℤ) =
        3 * (Nat.fib (2 * n + 3) : ℤ) := by
    exact_mod_cast hNat
  unfold markovFib
  rw [show 2 * (n + 2) + 1 = 2 * n + 5 by omega]
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
  linarith

private theorem fibonacciSpine_even_aux (n : ℕ) :
    (sternNode (List.replicate (2 * n) true)).state =
        ⟨1, markovFib (2 * n), markovFib (2 * n + 1)⟩ ∧
      (sternNode (List.replicate (2 * n) true)).back = .third := by
  induction n with
  | zero =>
      constructor
      · norm_num [sternNode, follow, orientedRoot, markovFib]
      · rfl
  | succ n ih =>
      rcases ih with ⟨hstate, hback⟩
      let node := sternNode (List.replicate (2 * n) true)
      have hstate' :
          node.state = ⟨1, markovFib (2 * n), markovFib (2 * n + 1)⟩ := by
        simpa [node] using hstate
      have hback' : node.back = .third := by
        simpa [node] using hback
      have hrec1 :
          markovFib (2 * n + 2) =
            3 * markovFib (2 * n + 1) - markovFib (2 * n) := by
        simpa only using markovFib_vieta_recurrence (2 * n)
      have hfirstState :
          (child node true).state =
            ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 1)⟩ := by
        change move (forwardMove node.back true) node.state =
          ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 1)⟩
        rw [hback', hstate']
        simp [forwardMove, move, MarkovEquation.jump, hrec1]
      have hfirstBack : (child node true).back = .second := by
        change forwardMove node.back true = .second
        rw [hback']
        rfl
      have hrec2 :
          markovFib (2 * n + 3) =
            3 * markovFib (2 * n + 2) - markovFib (2 * n + 1) := by
        simpa only [
          show (2 * n + 1) + 2 = 2 * n + 3 by omega,
          show (2 * n + 1) + 1 = 2 * n + 2 by omega
        ] using markovFib_vieta_recurrence (2 * n + 1)
      have hsecondState :
          (child (child node true) true).state =
            ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 3)⟩ := by
        change move (forwardMove (child node true).back true) (child node true).state =
          ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 3)⟩
        rw [hfirstBack, hfirstState]
        simp [forwardMove, move, MarkovEquation.jump, hrec2]
      have hsecondBack : (child (child node true) true).back = .third := by
        change forwardMove (child node true).back true = .third
        rw [hfirstBack]
        rfl
      have hrepl :
          List.replicate (2 * (n + 1)) true =
            true :: true :: List.replicate (2 * n) true := by
        rw [show 2 * (n + 1) = (2 * n).succ.succ by omega]
        rfl
      rw [hrepl, sternNode_cons, sternNode_cons]
      constructor
      · simpa only [
          show 2 * (n + 1) = 2 * n + 2 by omega,
          show 2 * (n + 1) + 1 = 2 * n + 3 by omega
        ] using hsecondState
      · simpa [node] using hsecondBack

/-- At every even depth on the all-right Stern-Brocot path, the Markov state is
`(1, F_(4n+1), F_(4n+3))`, expressed through `markovFib`. -/
theorem sternNode_fibonacciSpine_even (n : ℕ) :
    (sternNode (List.replicate (2 * n) true)).state =
      ⟨1, markovFib (2 * n), markovFib (2 * n + 1)⟩ :=
  (fibonacciSpine_even_aux n).1

/-- At every odd depth on the all-right Stern-Brocot path, the same two consecutive odd-index
Fibonacci numbers occur in the opposite coordinate order:
`(1, F_(4n+5), F_(4n+3))`. -/
theorem sternNode_fibonacciSpine_odd (n : ℕ) :
    (sternNode (List.replicate (2 * n + 1) true)).state =
      ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 1)⟩ := by
  have heven := fibonacciSpine_even_aux n
  let node := sternNode (List.replicate (2 * n) true)
  have hstate :
      node.state = ⟨1, markovFib (2 * n), markovFib (2 * n + 1)⟩ := by
    simpa [node] using heven.1
  have hback : node.back = .third := by
    simpa [node] using heven.2
  have hrec :
      markovFib (2 * n + 2) =
        3 * markovFib (2 * n + 1) - markovFib (2 * n) := by
    simpa only using markovFib_vieta_recurrence (2 * n)
  have hchild :
      (child node true).state =
        ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 1)⟩ := by
    change move (forwardMove node.back true) node.state =
      ⟨1, markovFib (2 * n + 2), markovFib (2 * n + 1)⟩
    rw [hback, hstate]
    simp [forwardMove, move, MarkovEquation.jump, hrec]
  have hrepl :
      List.replicate (2 * n + 1) true =
        true :: List.replicate (2 * n) true := by
    rw [show 2 * n + 1 = (2 * n).succ by omega]
    rfl
  rw [hrepl, sternNode_cons]
  simpa [node] using hchild

end LeanFrontier.MarkovTree

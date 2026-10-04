import LeanFrontier.NumberTheory.SternBrocot.RunLength
import Mathlib.Tactic

/-!
# Canonical run-length encoding of Stern-Brocot paths

The accepted Stern-Brocot / Euclidean interface can peel one maximal initial Boolean run and
identify the corresponding Euclidean quotient. This module packages that operation recursively
across an entire path.

`runLengthEncode` records each maximal constant run as a direction/length pair. It is defined in
terms of the accepted `initialRunLength` and `dropInitialRun` operations, so it uses the same
canonical run boundary as `initialRun_euclidean_step`.

The main reconstruction theorem proves that expanding the encoded runs recovers the original
path exactly. A second theorem records that every emitted run has positive length. Together these
give a reusable whole-path representation for the next Stern-Brocot / Euclidean-algorithm /
continued-fraction bridge.
-/

namespace LeanFrontier.SternBrocot

private theorem dropInitialRun_length_lt (dir : Bool) (tail : List Bool) :
    (dropInitialRun dir (dir :: tail)).length < (dir :: tail).length := by
  have hk : 0 < initialRunLength dir (dir :: tail) := by
    simp [initialRunLength]
  have hlen :
      (dir :: tail).length =
        initialRunLength dir (dir :: tail) +
          (dropInitialRun dir (dir :: tail)).length := by
    simpa using
      congrArg List.length (initialRun_decomposition dir (dir :: tail))
  calc
    (dropInitialRun dir (dir :: tail)).length <
        initialRunLength dir (dir :: tail) +
          (dropInitialRun dir (dir :: tail)).length :=
      Nat.lt_add_of_pos_left hk
    _ = (dir :: tail).length := hlen.symm

/-- Compress a Boolean path into its maximal constant runs.

Each pair stores the direction of one run and its positive length. The recursion removes the
accepted canonical maximal initial run before continuing, rather than introducing a second notion
of where run boundaries occur. -/
def runLengthEncode : List Bool → List (Bool × ℕ)
  | [] => []
  | dir :: tail =>
      (dir, initialRunLength dir (dir :: tail)) ::
        runLengthEncode (dropInitialRun dir (dir :: tail))
termination_by path => path.length
decreasing_by
  exact dropInitialRun_length_lt dir tail

/-- Expand a direction/length run encoding back to a Boolean path. -/
def expandRuns : List (Bool × ℕ) → List Bool
  | [] => []
  | (dir, n) :: runs => List.replicate n dir ++ expandRuns runs

/-- Expanding the canonical run-length encoding recovers the original path exactly. -/
theorem expandRuns_runLengthEncode : ∀ path : List Bool,
    expandRuns (runLengthEncode path) = path
  | [] => by
      rw [runLengthEncode, expandRuns]
  | dir :: tail => by
      rw [runLengthEncode, expandRuns]
      rw [expandRuns_runLengthEncode (dropInitialRun dir (dir :: tail))]
      exact (initialRun_decomposition dir (dir :: tail)).symm
termination_by path => path.length
decreasing_by
  exact dropInitialRun_length_lt dir tail

/-- Every block in the canonical run-length encoding has positive length. -/
theorem runLengthEncode_lengths_pos : ∀ path : List Bool,
    ∀ run ∈ runLengthEncode path, 0 < run.2
  | [] => by
      simp [runLengthEncode]
  | dir :: tail => by
      intro run hrun
      simp only [runLengthEncode, List.mem_cons] at hrun
      rcases hrun with hrun | hrun
      · subst run
        simp [initialRunLength]
      · exact
          runLengthEncode_lengths_pos
            (dropInitialRun dir (dir :: tail)) run hrun
termination_by path => path.length
decreasing_by
  exact dropInitialRun_length_lt dir tail

end LeanFrontier.SternBrocot

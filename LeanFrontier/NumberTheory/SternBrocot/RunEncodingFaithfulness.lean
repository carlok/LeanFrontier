import LeanFrontier.NumberTheory.SternBrocot.RunEncoding
import Mathlib.Tactic

/-!
# Faithfulness and length accounting for Stern-Brocot run encoding

The canonical run-length encoding of a Stern-Brocot path already has a left inverse:
expanding the emitted runs reconstructs the path. This module promotes that
reconstruction into injectivity of the encoding, and accounts for the entire
path length as the sum of its canonical run lengths.

The length identity first holds for *arbitrary* lists of direction/length pairs,
including pairs with zero length; it is then specialized to canonical encodings.
-/

namespace LeanFrontier.SternBrocot

/-- Canonical run-length encoding distinguishes any two Stern-Brocot paths. -/
theorem runLengthEncode_injective : Function.Injective runLengthEncode := by
  intro p q h
  calc
    p = expandRuns (runLengthEncode p) := (expandRuns_runLengthEncode p).symm
    _ = expandRuns (runLengthEncode q) := congrArg expandRuns h
    _ = q := expandRuns_runLengthEncode q

/-- Expanding a list of runs produces exactly the sum of their lengths. -/
theorem expandRuns_length (runs : List (Bool × ℕ)) :
    (expandRuns runs).length = (runs.map Prod.snd).sum := by
  induction runs with
  | nil =>
      simp [expandRuns]
  | cons run tail ih =>
      rcases run with ⟨dir, n⟩
      simp [expandRuns, ih]

/-- A Stern-Brocot path's length is the sum of its canonical run lengths. -/
theorem runLengthEncode_sum_lengths (path : List Bool) :
    ((runLengthEncode path).map Prod.snd).sum = path.length := by
  calc
    ((runLengthEncode path).map Prod.snd).sum =
        (expandRuns (runLengthEncode path)).length :=
      (expandRuns_length (runLengthEncode path)).symm
    _ = path.length := congrArg List.length (expandRuns_runLengthEncode path)

end LeanFrontier.SternBrocot

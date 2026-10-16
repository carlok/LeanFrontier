import LeanFrontier.NumberTheory.SternBrocot.ContinuedFraction
import LeanFrontier.NumberTheory.SternBrocot.RunEncoding
import Mathlib.Data.List.ModifyLast
import Mathlib.Tactic

/-!
# Stern–Brocot Euclidean quotients from canonical maximal runs

The canonical run-length encoding and the Euclidean quotient sequence in
LeanFrontier previously peeled the same maximal initial runs through separate
recursive definitions. This module proves that the quotient list is exactly
the list of encoded run lengths, with the terminal length incremented by one.

This identifies the path's *actual* continued-fraction coefficients with its
canonical run encoding, rather than introducing any additional path encoding.
The root path requires a separate convention: its quotient list is `[1]`,
whereas the empty path has no Boolean runs.
-/

namespace LeanFrontier.SternBrocot

/-- The Euclidean quotients of a nonempty Stern–Brocot path are its canonical
maximal-run lengths, with precisely the final length incremented by one.

The run directions are discarded because they are irrelevant to the sequence
of Euclidean quotients; the final increment is Euclid's terminal convention. -/
theorem pathQuotients_eq_runLengthEncode :
    ∀ path : List Bool, path ≠ [] →
      pathQuotients path =
        List.modifyLast Nat.succ ((runLengthEncode path).map Prod.snd)
  | [], h => (h rfl).elim
  | dir :: tail, _ => by
      let path := dir :: tail
      let k := initialRunLength dir path
      let rest := dropInitialRun dir path
      have hlen : rest.length < path.length := by
        have hk : 0 < k := by
          simp [k, path, initialRunLength]
        have hdecomp :
            path.length = k + rest.length := by
          simpa [path, k, rest] using
            congrArg List.length (initialRun_decomposition dir path)
        omega
      rw [pathQuotients, runLengthEncode]
      dsimp only [List.map_cons, Prod.snd]
      change (if rest = [] then [k + 1] else k :: pathQuotients rest) =
        List.modifyLast Nat.succ
          (k :: (runLengthEncode rest).map Prod.snd)
      by_cases hrest : rest = []
      · rw [if_pos hrest]
        simpa [hrest, Nat.succ_eq_add_one] using
          (List.modifyLast_concat Nat.succ k [])
      · have ih := pathQuotients_eq_runLengthEncode rest hrest
        have hnonempty : (runLengthEncode rest).map Prod.snd ≠ [] := by
          cases rest with
          | nil => contradiction
          | cons d ds =>
              simp [runLengthEncode]
        have hmodify :
            List.modifyLast Nat.succ
                (k :: (runLengthEncode rest).map Prod.snd) =
              k :: List.modifyLast Nat.succ
                ((runLengthEncode rest).map Prod.snd) := by
          simpa using
            (List.modifyLast_append_of_right_ne_nil Nat.succ [k]
              ((runLengthEncode rest).map Prod.snd) hnonempty)
        rw [if_neg hrest, hmodify, ← ih]
termination_by path => path.length
decreasing_by
  exact hlen

/-- The quotient/run correspondence including the exceptional root path. -/
theorem pathQuotients_eq_runLengthEncode_all (path : List Bool) :
    pathQuotients path =
      if path = [] then [1] else
        List.modifyLast Nat.succ ((runLengthEncode path).map Prod.snd) := by
  cases path with
  | nil => simp [pathQuotients]
  | cons d ds =>
      simp only [List.cons_ne_nil, ↓reduceIte]
      exact pathQuotients_eq_runLengthEncode (d :: ds) (List.cons_ne_nil _ _)

/-- The quotients obtained by Euclid's algorithm on a Stern–Brocot rational
are obtained *directly* from the path's canonical run-length encoding. -/
theorem euclideanRunQuotients_pair_eq_runLengthEncode (path : List Bool) :
    euclideanRunQuotients (pair path).1 (pair path).2 =
      if path = [] then [1] else
        List.modifyLast Nat.succ ((runLengthEncode path).map Prod.snd) := by
  rw [euclideanRunQuotients_pair, pathQuotients_eq_runLengthEncode_all]

/-- The coefficients of the regular continued fraction attached to a
nonempty Stern–Brocot path are exactly its canonical run lengths, with a
terminal increment and the conventional leading zero on left-going paths. -/
theorem regularCoefficients_eq_runLengthEncode
    (dir : Bool) (tail : List Bool) :
    regularCoefficients (dir :: tail) =
      (if dir then [] else [0]) ++
        List.modifyLast Nat.succ
          ((runLengthEncode (dir :: tail)).map Prod.snd) := by
  rw [regularCoefficients_runs]
  have hquot :=
    pathQuotients_eq_runLengthEncode (dir :: tail)
      (List.cons_ne_nil _ _)
  cases dir <;> simp_all

end LeanFrontier.SternBrocot

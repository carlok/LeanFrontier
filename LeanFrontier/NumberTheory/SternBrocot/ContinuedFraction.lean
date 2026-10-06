import LeanFrontier.NumberTheory.SternBrocot.QuotientSequence
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Stern-Brocot paths and regular continued fractions

The accepted Stern-Brocot development now identifies every complete path-run quotient sequence with
the symmetric Euclidean algorithm on the represented numerator-denominator pair. This module
connects that arithmetic interface to Mathlib's actual regular continued-fraction computation,
`GenContFract.of`.

For a positive rational below one, a regular continued fraction has the conventional leading zero;
the symmetric Euclidean quotient sequence deliberately omitted it. `regularCoefficients` restores
exactly that zero when needed. The theorem `regularCoefficients_runs` then states the complete
binary-path dictionary: these coefficients are the canonical Stern-Brocot run quotients, with a
leading zero precisely for an initial left move.

`natCoefficientsGCF` packages a finite list of natural coefficients as a simple
`GenContFract ℚ`. The main theorem `genContFract_pair` proves that Mathlib's computed continued
fraction of the rational represented by a Stern-Brocot path is exactly that finite object.
-/

namespace LeanFrontier.SternBrocot

private def coefficientPair (n : ℕ) : GenContFract.Pair ℚ :=
  ⟨1, n⟩

/-- A finite regular continued fraction whose coefficients are natural numbers.

The first list entry is the head coefficient. Every later entry is used as a partial denominator
with partial numerator one. The empty list is represented by the zero integer continued fraction;
it is only a totality convention and does not occur in the path theorem below. -/
def natCoefficientsGCF : List ℕ → GenContFract ℚ
  | [] => GenContFract.ofInteger 0
  | h :: tail =>
      ⟨h, Stream'.Seq.ofList (tail.map coefficientPair)⟩

/-- Regular continued-fraction coefficients attached to a Stern-Brocot path.

The accepted symmetric Euclidean quotient sequence omits the leading zero of rationals below one.
This definition restores that zero exactly when the represented numerator is smaller than the
denominator. -/
def regularCoefficients (path : List Bool) : List ℕ :=
  let p := pair path
  if p.1 < p.2 then
    0 :: euclideanRunQuotients p.1 p.2
  else
    euclideanRunQuotients p.1 p.2

private def standardEuclideanQuotients : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, b + 1 =>
      a / (b + 1) ::
        standardEuclideanQuotients (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by
  exact Nat.mod_lt _ (Nat.succ_pos _)

private theorem standardEuclideanQuotients_of_pos (a b : ℕ) (hb : 0 < b) :
    standardEuclideanQuotients a b =
      a / b :: standardEuclideanQuotients b (a % b) := by
  cases b with
  | zero => omega
  | succ b =>
      rw [standardEuclideanQuotients]

private theorem standardEuclideanQuotients_eq_adjusted :
    ∀ a b : ℕ, 0 < a → 0 < b →
      standardEuclideanQuotients a b =
        if a < b then
          0 :: euclideanRunQuotients a b
        else
          euclideanRunQuotients a b
  | 0, _, ha, _ => by
      omega
  | _, 0, _, hb => by
      omega
  | a + 1, b + 1, _, _ => by
      by_cases hab : a + 1 < b + 1
      · have hdiv : (a + 1) / (b + 1) = 0 := Nat.div_eq_of_lt hab
        have hmod : (a + 1) % (b + 1) = a + 1 := Nat.mod_eq_of_lt hab
        rw [standardEuclideanQuotients, hdiv, hmod]
        rw [if_pos hab]
        rw [euclideanRunQuotients]
        simp only [hab, if_true]
        congr 1
        rw [standardEuclideanQuotients]
        let r := (b + 1) % (a + 1)
        have hrlt : r < a + 1 := Nat.mod_lt _ (Nat.succ_pos a)
        by_cases hr : r = 0
        · simp [r, hr, standardEuclideanQuotients, euclideanRunQuotients]
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hrec :=
            standardEuclideanQuotients_eq_adjusted (a + 1) r (Nat.succ_pos a) hrpos
          have hnot : ¬ a + 1 < r := by omega
          rw [if_neg hnot] at hrec
          simpa [r] using hrec
      · rw [standardEuclideanQuotients]
        rw [if_neg hab]
        rw [euclideanRunQuotients]
        simp only [hab, if_false]
        congr 1
        let r := (a + 1) % (b + 1)
        have hrlt : r < b + 1 := Nat.mod_lt _ (Nat.succ_pos b)
        by_cases hr : r = 0
        · simp [r, hr, standardEuclideanQuotients, euclideanRunQuotients]
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hrec :=
            standardEuclideanQuotients_eq_adjusted r (b + 1) hrpos (Nat.succ_pos b)
          rw [if_pos hrlt] at hrec
          have hdiv : r / (b + 1) = 0 := Nat.div_eq_of_lt hrlt
          have hmod : r % (b + 1) = r := Nat.mod_eq_of_lt hrlt
          rw [standardEuclideanQuotients_of_pos r (b + 1) (Nat.succ_pos b),
            hdiv, hmod] at hrec
          exact List.cons.inj hrec |>.2
termination_by a b _ _ => a + b
decreasing_by
  all_goals
    dsimp only
    omega

private theorem nat_div_eq_natCast_of_mod_eq_zero
    (a b : ℕ) (hb : 0 < b) (hmod : a % b = 0) :
    ((a : ℚ) / (b : ℚ)) = ((a / b : ℕ) : ℚ) := by
  have hmul : b * (a / b) = a := by
    have h := Nat.mod_add_div a b
    simpa [hmod] using h
  rw [div_eq_iff (by positivity)]
  norm_cast
  simpa [Nat.mul_comm] using hmul.symm

private theorem genContFract_of_nat_div_standard :
    ∀ a b : ℕ, 0 < b →
      GenContFract.of ((a : ℚ) / (b : ℚ)) =
        natCoefficientsGCF (standardEuclideanQuotients a b)
  | _, 0, hb => by
      omega
  | a, b + 1, _ => by
      have hbpos : 0 < b + 1 := Nat.succ_pos b
      rw [standardEuclideanQuotients]
      apply GenContFract.ext
      · rw [GenContFract.of_h_eq_floor, Rat.floor_natCast_div_natCast]
        rfl
      · let r := a % (b + 1)
        have hrlt : r < b + 1 := Nat.mod_lt _ hbpos
        by_cases hr : r = 0
        · have hq :
              ((a : ℚ) / (b + 1 : ℕ)) =
                (((a / (b + 1) : ℕ) : ℤ) : ℚ) := by
            simpa [Int.cast_natCast] using
              nat_div_eq_natCast_of_mod_eq_zero a (b + 1) hbpos (by simpa [r] using hr)
          have hs :=
            GenContFract.of_s_of_int ℚ (((a / (b + 1) : ℕ) : ℤ))
          rw [hq]
          simpa [natCoefficientsGCF, r, hr, standardEuclideanQuotients] using hs
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          let q : ℚ := (a : ℚ) / (b + 1 : ℕ)
          have hfract :
              Int.fract q = (r : ℚ) / (b + 1 : ℕ) := by
            simpa [q, r] using
              (Int.fract_div_natCast_eq_div_natCast_mod
                (k := ℚ) (m := a) (n := b + 1))
          have hfract_ne : Int.fract q ≠ 0 := by
            rw [hfract]
            positivity
          have hhead0 := GenContFract.of_s_head (v := q) hfract_ne
          have hhead :
              (GenContFract.of q).s.head =
                some (coefficientPair ((b + 1) / r)) := by
            rw [hfract, inv_div, Rat.floor_natCast_div_natCast] at hhead0
            simpa [coefficientPair] using hhead0
          have htail0 := GenContFract.of_s_tail q
          have htail :
              (GenContFract.of q).s.tail =
                (GenContFract.of ((b + 1 : ℕ) / (r : ℚ))).s := by
            rw [hfract, inv_div] at htail0
            simpa using htail0
          have hchild :=
            genContFract_of_nat_div_standard (b + 1) r hrpos
          have hchildStep :=
            standardEuclideanQuotients_of_pos (b + 1) r hrpos
          have hchildS :
              (GenContFract.of ((b + 1 : ℕ) / (r : ℚ))).s =
                Stream'.Seq.ofList
                  ((standardEuclideanQuotients r ((b + 1) % r)).map coefficientPair) := by
            rw [hchildStep] at hchild
            simpa [natCoefficientsGCF] using congrArg GenContFract.s hchild
          have hseq :
              (GenContFract.of q).s =
                Stream'.Seq.cons
                  (coefficientPair ((b + 1) / r))
                  (GenContFract.of ((b + 1 : ℕ) / (r : ℚ))).s := by
            calc
              (GenContFract.of q).s =
                  Stream'.Seq.cons
                    (coefficientPair ((b + 1) / r))
                    (GenContFract.of q).s.tail :=
                Stream'.Seq.head_eq_some hhead
              _ =
                  Stream'.Seq.cons
                    (coefficientPair ((b + 1) / r))
                    (GenContFract.of ((b + 1 : ℕ) / (r : ℚ))).s := by
                rw [htail]
          rw [hseq, hchildS]
          rw [← Stream'.Seq.ofList_cons, ← List.map_cons]
          rw [← standardEuclideanQuotients_of_pos (b + 1) r hrpos]
          rfl
termination_by a b _ => b
decreasing_by
  exact hrlt

/-- The regular coefficients are exactly the accepted canonical Stern-Brocot run quotients,
except that an initial left move contributes the conventional regular-CF leading zero. -/
theorem regularCoefficients_runs (path : List Bool) :
    regularCoefficients path =
      match path with
      | [] => pathQuotients []
      | false :: tail => 0 :: pathQuotients (false :: tail)
      | true :: tail => pathQuotients (true :: tail) := by
  have hp := pair_positive_coprime path
  have hrel :=
    standardEuclideanQuotients_eq_adjusted
      (pair path).1 (pair path).2 hp.1 hp.2.1
  rw [euclideanRunQuotients_pair path] at hrel
  unfold regularCoefficients
  rw [← hrel]
  cases path with
  | nil =>
      simp [pair]
  | cons dir tail =>
      cases dir
      · have htail := pair_positive_coprime tail
        have hlt : (pair (false :: tail)).1 < (pair (false :: tail)).2 := by
          simp only [pair]
          omega
        simp [hlt]
      · have htail := pair_positive_coprime tail
        have hnlt : ¬ (pair (true :: tail)).1 < (pair (true :: tail)).2 := by
          simp only [pair]
          omega
        simp [hnlt]

/-- Mathlib's computed regular continued fraction of the rational at a Stern-Brocot path is the
finite simple continued fraction obtained from that path's complete Euclidean/run coefficients. -/
theorem genContFract_pair (path : List Bool) :
    GenContFract.of
        (((pair path).1 : ℚ) / ((pair path).2 : ℚ)) =
      natCoefficientsGCF (regularCoefficients path) := by
  have hp := pair_positive_coprime path
  have hstd :=
    genContFract_of_nat_div_standard (pair path).1 (pair path).2 hp.2.1
  have hrel :=
    standardEuclideanQuotients_eq_adjusted
      (pair path).1 (pair path).2 hp.1 hp.2.1
  rw [hrel] at hstd
  simpa [regularCoefficients] using hstd

end LeanFrontier.SternBrocot

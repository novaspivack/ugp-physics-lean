import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds

open Real

/-!
# H9: IPT Self-Consistency Fixed Point

IPT is the unique fixed point of the map T(x) = 1/(1 − ln2/N(x))
where N(x) = ln2·(lnφ + 2·ln(2π))/lnφ is determined by x's derivation
constants (golden ratio φ and 2π).

This file proves the algebraic identity:
  1/(1 − ln2/N_universal) = IPT

where:
  φ   = (1 + √5)/2
  IPT = 1 + lnφ / (2·ln(2π))
  N   = ln2·(lnφ + 2·ln(2π)) / lnφ

The identity holds as an exact algebraic consequence of these definitions.
-/

-- The golden ratio
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

-- Basic positivity lemmas for phi
lemma phi_pos : 0 < phi := by
  unfold phi
  have hsqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

lemma phi_gt_one : 1 < phi := by
  unfold phi
  have h5 : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    apply Real.sqrt_lt_sqrt
    · norm_num
    · norm_num
  linarith

-- Log positivity lemmas
lemma log_phi_pos : 0 < Real.log phi := Real.log_pos phi_gt_one

lemma log_phi_ne_zero : Real.log phi ≠ 0 := ne_of_gt log_phi_pos

lemma two_pi_gt_one : 1 < 2 * Real.pi := by
  linarith [Real.pi_gt_three]

lemma log_two_pi_pos : 0 < Real.log (2 * Real.pi) :=
  Real.log_pos two_pi_gt_one

lemma log_two_pi_ne_zero : Real.log (2 * Real.pi) ≠ 0 := ne_of_gt log_two_pi_pos

-- N_universal: the Landauer overhead denominator determined by φ and 2π
noncomputable def N_universal : ℝ :=
  Real.log 2 * (Real.log phi + 2 * Real.log (2 * Real.pi)) / Real.log phi

-- IPT: the information-theoretic selection threshold
noncomputable def IPT_val : ℝ :=
  1 + Real.log phi / (2 * Real.log (2 * Real.pi))

-- Key non-zero denominators needed for the proof
lemma N_universal_denom_ne_zero :
    Real.log phi + 2 * Real.log (2 * Real.pi) ≠ 0 := by
  have h1 : 0 < Real.log phi := log_phi_pos
  have h2 : 0 < Real.log (2 * Real.pi) := log_two_pi_pos
  linarith

lemma log_2_pos : 0 < Real.log 2 := by
  apply Real.log_pos; norm_num

lemma log_2_ne_zero : Real.log 2 ≠ 0 := ne_of_gt log_2_pos

lemma N_universal_ne_zero : N_universal ≠ 0 := by
  unfold N_universal
  have h1 : 0 < Real.log 2 := log_2_pos
  have h2 : 0 < Real.log phi + 2 * Real.log (2 * Real.pi) := by
    have := log_phi_pos; have := log_two_pi_pos; linarith
  have h3 : 0 < Real.log phi := log_phi_pos
  positivity

/-!
## Main Theorem: IPT is a self-consistent fixed point

Proof sketch:
  ln2/N = ln2 × lnφ / [ln2·(lnφ + 2·ln(2π))] = lnφ/(lnφ + 2·ln(2π))
  1 − ln2/N = 2·ln(2π)/(lnφ + 2·ln(2π))
  1/(1 − ln2/N) = (lnφ + 2·ln(2π))/(2·ln(2π)) = 1 + lnφ/(2·ln(2π)) = IPT ✓
-/
theorem ipt_self_consistent :
    1 / (1 - Real.log 2 / N_universal) = IPT_val := by
  unfold N_universal IPT_val
  have hphi : Real.log phi ≠ 0 := log_phi_ne_zero
  have h2pi : Real.log (2 * Real.pi) ≠ 0 := log_two_pi_ne_zero
  have hsum : Real.log phi + 2 * Real.log (2 * Real.pi) ≠ 0 :=
    N_universal_denom_ne_zero
  have hlog2 : Real.log 2 ≠ 0 := log_2_ne_zero
  field_simp
  ring

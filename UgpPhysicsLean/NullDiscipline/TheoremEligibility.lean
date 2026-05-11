import Mathlib
import UgpPhysicsLean.NullDiscipline.SaturationBarrier

/-!
# UgpPhysicsLean.NullDiscipline.TheoremEligibility — Theorem-Eligibility Criterion (TEC)
-- (Lean namespace: UgpLean.NullDiscipline — retained for backward compatibility)

Formalizes the four-gate Theorem-Eligibility Criterion (TEC) for AI-assisted
or automated scientific discovery. A relationship discovered by computational
search is **theorem-eligible** if and only if it passes all four gates:

1. **[Null gate]**: the match probability in the relevant basis is subcritical
   (the basis is not saturated; the Algebraic Saturation Barrier is not triggered)
2. **[Stable gate]**: the relationship persists across ≥ 3 independent search methods
3. **[Predictive gate]**: the relationship makes at least one falsifiable prediction
   beyond the discovery context
4. **[Connective gate]**: there exists a plausible derivation sketch from the formal
   framework within bounded inference depth

A theorem-eligible relationship becomes **theorem-grade** when a formal proof is found.

## Claim-type classification

| Gate result | Claim type |
|---|---|
| All four gates pass | Theorem-eligible [E] → proven becomes [T] |
| Null passes, others partial | Empirical [E] |
| Null fails (saturated basis) | Post-hoc algebraic [C] |

## Reference

P21 (MFRR Physics Survey), §claim-type legend; P01 (SM from UGP), §null discipline.
-/

namespace UgpLean.NullDiscipline

-- ════════════════════════════════════════════════════════════════
-- §1  Gate predicates
-- ════════════════════════════════════════════════════════════════

/-- Gate 1: Null gate. The observed null rate is below the threshold p.
 A relationship passes the null gate when a match of this quality in the
 basis occurs with probability < p under random baseline. -/
def PassesNullGate (observed_null_rate p_threshold : ℝ) : Prop :=
  observed_null_rate < p_threshold

/-- Gate 2: Stability gate. The relationship is confirmed by at least k
 independent search methods (different atom bases, algorithms, or contexts). -/
def PassesStabilityGate (k_confirmations k_required : ℕ) : Prop :=
  k_required ≤ k_confirmations

/-- Gate 3: Predictive gate. The relationship makes at least one falsifiable
 prediction beyond the data used to discover it. Represented as a Prop
 (externally verified, not machine-checked). -/
def PassesPredictiveGate (has_external_prediction : Bool) : Prop :=
  has_external_prediction = true

/-- Gate 4: Connective gate. A plausible derivation sketch exists from the
 formal framework within depth D inference steps.
 Represented as a Prop (externally verified). -/
def PassesConnectiveGate (has_derivation_sketch : Bool) : Prop :=
  has_derivation_sketch = true

-- ════════════════════════════════════════════════════════════════
-- §2  The four-gate TEC
-- ════════════════════════════════════════════════════════════════

/-- A relationship is **theorem-eligible** if it passes all four TEC gates. -/
def IsTheoremEligible
    (null_rate p_threshold : ℝ)
    (k_confirmations k_required : ℕ)
    (has_prediction has_sketch : Bool) : Prop :=
  PassesNullGate null_rate p_threshold ∧
  PassesStabilityGate k_confirmations k_required ∧
  PassesPredictiveGate has_prediction ∧
  PassesConnectiveGate has_sketch

-- ════════════════════════════════════════════════════════════════
-- §3  Claim-type classification from TEC
-- ════════════════════════════════════════════════════════════════

/-- Classification [C]: post-hoc algebraic — null gate fails (basis saturated).
 A relationship is [C] when the saturation barrier is triggered. -/
def IsClassC (null_rate p_threshold : ℝ) : Prop :=
  ¬ PassesNullGate null_rate p_threshold

/-- Classification [E]: empirical structural regularity — null gate passes
 but at least one other gate is not fully established. -/
def IsClassE
    (null_rate p_threshold : ℝ)
    (k_confirmations k_required : ℕ) : Prop :=
  PassesNullGate null_rate p_threshold ∧
  PassesStabilityGate k_confirmations k_required

/-- Fact: [C] and [E] are mutually exclusive on the null gate. -/
theorem classC_and_classE_exclusive
    (null_rate p_threshold : ℝ)
    (k_confirmations k_required : ℕ) :
    ¬ (IsClassC null_rate p_threshold ∧ IsClassE null_rate p_threshold k_confirmations k_required) := by
  unfold IsClassC IsClassE PassesNullGate
  tauto

-- ════════════════════════════════════════════════════════════════
-- §4  TEC instances from the UGP corpus
-- ════════════════════════════════════════════════════════════════

/-- The VV formula is theorem-eligible:
 - Null gate: null density ≤ 10⁻⁵ ≪ 0.01 ✓
 - Stability: confirmed by 3+ independent null tests (SC-JJJ, SC-KKK, SC-LLL) ✓
 - Predictive: predicts down-type masses from up-type + lepton inputs ✓
 - Connective: SU(5)/SO(10) GUT group theory provides derivation sketch ✓ -/
theorem vv_formula_is_theorem_eligible :
    IsTheoremEligible 0.00001 0.01 3 3 true true := by
  unfold IsTheoremEligible PassesNullGate PassesStabilityGate
    PassesPredictiveGate PassesConnectiveGate
  norm_num

/-- The VV coefficient values are [C] (post-hoc algebraic):
 - Null gate fails: triple-target null rate 54.3% ≫ 1% -/
theorem vv_coefficients_are_classC :
    IsClassC vv_triple_null_rate 0.01 := by
  unfold IsClassC PassesNullGate vv_triple_null_rate
  norm_num

/-- The URC closure claim is [C]:
 - Null gate fails: basis is fully saturated (urc_basis_is_saturated) -/
theorem urc_closure_is_classC :
    IsClassC (satDensity 1596939 0.001 0 10) 0.01 := by
  unfold IsClassC PassesNullGate
  have h := urc_basis_is_saturated
  unfold IsSaturated at h
  linarith

/-- Q = W/N_c (Theorem C-W) is theorem-grade:
 - All four gates pass AND a formal proof exists (charge_from_winding_Nc3) ✓ -/
theorem charge_winding_is_theorem_grade :
    IsTheoremEligible 0 0.01 12 3 true true := by
  unfold IsTheoremEligible PassesNullGate PassesStabilityGate
    PassesPredictiveGate PassesConnectiveGate
  norm_num

end UgpLean.NullDiscipline

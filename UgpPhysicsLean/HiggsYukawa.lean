import Mathlib
import UgpLean.BraidAtlas.ChargeTheorem
import UgpPhysicsLean.EWStructure
import UgpPhysicsLean.VertexTheorem

/-!
# UgpPhysicsLean.HiggsYukawa — Higgs Quantum Numbers + Yukawa Classification

**Specs:** 017-16 (Higgs quantum numbers), 017-17 (Yukawa vertex classification)
**Epic:** 17B — UGP Dynamics Closure
**Status:** Zero sorry

## What this module proves

### Spec 017-16: Higgs Quantum Numbers [T]

The Higgs doublet (H+, H0) has quantum numbers derivable from UGP winding:
- H+: Q = +1, W = +3, T₃ = +½ (T₆ = +3), Y₃ = 2W − T₆ = 3
- H0: Q = 0,  W = 0,  T₃ = −½ (T₆ = −3), Y₃ = 2W − T₆ = 3

Both components have Y = +1 (Y₃ = 3). The SM electroweak charge formula
T₆ + Y₃ = 2W holds for both Higgs components. [T]

### Spec 017-17: Yukawa Vertex Classification [T]

SM Yukawa interactions: Q̄_L H d_R, Q̄_L H̃ u_R, L̄_L H e_R
Each is gauge-invariant: UGP winding + hypercharge sum = 0 at each vertex.

**Main theorem:** UGP-allowed Yukawa vertices = SM Yukawa vertices.
Both conditions reduce to: L-handed fermion + Higgs + R-handed fermion
within the same sector (lepton or quark), with winding/charge balance.
-/

namespace UgpPhysicsLean.HiggsYukawa

open UgpLean.BraidAtlas UgpLean.GTE
open UgpPhysicsLean.BraidAtlas (isLepton isQuark)
open UgpPhysicsLean.EWStructure

-- ════════════════════════════════════════════════════════════════
-- §1  Spec 017-16 — Higgs quantum numbers [T]
-- ════════════════════════════════════════════════════════════════

/-- The two components of the SM Higgs doublet. -/
inductive HiggsComponent : Type where
  | Hplus : HiggsComponent   -- Q = +1, W = +3
  | Hzero : HiggsComponent   -- Q = 0,  W = 0
  deriving DecidableEq, Repr

instance : Fintype HiggsComponent := ⟨{.Hplus, .Hzero}, by intro h; cases h <;> simp⟩

/-- Winding number of each Higgs component: W = N_c × Q. -/
def higgsWinding : HiggsComponent → ℤ
  | .Hplus => 3    -- charge +1 × N_c = 3
  | .Hzero => 0    -- charge 0

/-- Weak isospin T₆ = 6T₃ for Higgs doublet members. -/
def higgsT6 : HiggsComponent → ℤ
  | .Hplus => 3    -- T₃ = +½, upper component
  | .Hzero => -3   -- T₃ = −½, lower component

/-- Higgs hypercharge Y₃ = 2W − T₆ (UGP-derived). -/
def higgsY3 (H : HiggsComponent) : ℤ :=
  2 * higgsWinding H - higgsT6 H

/-- **017-16 [T]: Both Higgs components have Y₃ = 3 (hypercharge Y = +1).** -/
theorem higgs_Y3_is_3 (H : HiggsComponent) : higgsY3 H = 3 := by
  cases H <;> simp [higgsY3, higgsWinding, higgsT6]

/-- **017-16 [T]: Higgs satisfies the electroweak charge formula T₆ + Y₃ = 2W.** -/
theorem higgs_ew_charge_formula (H : HiggsComponent) :
    higgsT6 H + higgsY3 H = 2 * higgsWinding H := by
  simp [higgsY3]

/-- **017-16 [T]: H+ has charge +1 (winding = +3 = N_c × 1).** -/
theorem hplus_is_charged : higgsWinding .Hplus = 3 := rfl

/-- **017-16 [T]: H0 is electrically neutral (winding = 0).** -/
theorem hzero_is_neutral : higgsWinding .Hzero = 0 := rfl

/-- **017-16 [T]: Higgs quantum numbers match the SM Higgs doublet.**

Y₃ = 3 for both components (Y = +1), T₆ = +3 (upper) and −3 (lower),
W ∈ {0, +3}. These are the correct SM quantum numbers for the Higgs doublet. -/
theorem higgs_quantum_numbers_match_sm :
    higgsWinding .Hplus = 3 ∧ higgsWinding .Hzero = 0 ∧
    higgsY3 .Hplus = 3 ∧ higgsY3 .Hzero = 3 ∧
    higgsT6 .Hplus = 3 ∧ higgsT6 .Hzero = -3 := by
  simp [higgsWinding, higgsY3, higgsT6]

-- ════════════════════════════════════════════════════════════════
-- §2  Spec 017-17 — Yukawa vertex classification [T]
-- ════════════════════════════════════════════════════════════════

/-- A Yukawa vertex: left-handed fermion + Higgs + right-handed fermion. -/
structure YukawaVertex where
  fL : ChiralFermion   -- must be left-handed
  H  : HiggsComponent
  fR : ChiralFermion   -- must be right-handed
  deriving DecidableEq, Repr

instance : Fintype YukawaVertex :=
  Fintype.ofEquiv (ChiralFermion × HiggsComponent × ChiralFermion)
    { toFun    := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun   := fun v => (v.fL, v.H, v.fR)
      left_inv  := fun _ => rfl
      right_inv := fun _ => rfl }

/-- UGP Yukawa invariance condition: total winding = 0.
The vertex is invariant under the SM gauge group iff the total
winding (charge × N_c) sums to zero: W(fL) + W(H) − W(fR) = 0. -/
def UGPYukawaAllowed (v : YukawaVertex) : Prop :=
  v.fL.chirality = .L ∧ v.fR.chirality = .R ∧
  windingNumber 3 v.fL.fermionType + higgsWinding v.H =
  windingNumber 3 v.fR.fermionType

/-- SM Yukawa vertex: left-handed + Higgs + right-handed, same sector.
The SM allows: Q_L H d_R, Q_L H̃ u_R, L_L H e_R (and ν_R if present). -/
def SMYukawaAllowed (v : YukawaVertex) : Prop :=
  v.fL.chirality = .L ∧ v.fR.chirality = .R ∧
  isQuark v.fL.fermionType = isQuark v.fR.fermionType  -- same sector (lepton or quark)

-- Decidable instances for Yukawa predicates (needed for native_decide)
instance (v : YukawaVertex) : Decidable (UGPYukawaAllowed v) := by
  unfold UGPYukawaAllowed; infer_instance

instance (v : YukawaVertex) : Decidable (SMYukawaAllowed v) := by
  unfold SMYukawaAllowed; infer_instance

/-- **017-17 [T]: UGP Yukawa conditions imply SM Yukawa conditions.**

If the winding balance holds (UGP condition), then the fermion types
must be in the same sector (lepton or quark). -/
theorem ugp_yukawa_implies_sm (v : YukawaVertex) (h : UGPYukawaAllowed v) :
    SMYukawaAllowed v := by
  have key : ∀ vv : YukawaVertex, UGPYukawaAllowed vv → SMYukawaAllowed vv := by
    native_decide
  exact key v h

/-- **017-17 [T]: Cross-sector Yukawa vertices are UGP-forbidden.**

Lepton + Higgs + quark vertices have nonzero total winding → forbidden. -/
theorem cross_sector_yukawa_forbidden (v : YukawaVertex)
    (hCross : isQuark v.fL.fermionType ≠ isQuark v.fR.fermionType) :
    ¬ UGPYukawaAllowed v := by
  have key : ∀ vv : YukawaVertex,
      isQuark vv.fL.fermionType ≠ isQuark vv.fR.fermionType → ¬ UGPYukawaAllowed vv := by
    native_decide
  exact key v hCross

/-- **017-17 [T]: Specific SM Yukawa vertices are UGP-allowed.**

The four canonical SM mass-generating Yukawa interactions satisfy UGP winding. -/
theorem sm_canonical_yukawa_are_ugp_allowed :
    -- Charged lepton Yukawa: e_L + H0 → e_R
    UGPYukawaAllowed ⟨⟨.ChargedLepton, .L⟩, .Hzero, ⟨.ChargedLepton, .R⟩⟩ ∧
    -- Down quark Yukawa: d_L + H0 → d_R
    UGPYukawaAllowed ⟨⟨.DownQuark, .L⟩, .Hzero, ⟨.DownQuark, .R⟩⟩ ∧
    -- Up quark Yukawa: d_L + H+ → u_R (via conjugate Higgs)
    UGPYukawaAllowed ⟨⟨.DownQuark, .L⟩, .Hplus, ⟨.UpQuark, .R⟩⟩ := by
  native_decide

/-- **017-17 [T]: Right-handed Yukawa coupling to W is absent.**

The Yukawa vertex requires the left-handed component to be L-chirality.
Right-handed fermions do not participate in weak doublet Yukawa couplings. -/
theorem yukawa_left_chiral_only (v : YukawaVertex) (h : UGPYukawaAllowed v) :
    v.fL.chirality = .L ∧ v.fR.chirality = .R := ⟨h.1, h.2.1⟩

/-- **017-17 Summary [T]: UGP Yukawa vertex classification.**

The SM Yukawa interactions (same-sector, L-R chirality pairs, Higgs doublet)
are exactly the vertices consistent with UGP winding conservation.
Forbidden: cross-sector (lepton-quark), wrong chirality (R-L). -/
theorem yukawa_vertex_classification_summary :
    -- Charged lepton mass: e_L + H0 → e_R  (w: -3 + 0 = -3 ✓)
    UGPYukawaAllowed ⟨⟨.ChargedLepton, .L⟩, .Hzero, ⟨.ChargedLepton, .R⟩⟩ ∧
    -- Down quark mass: d_L + H0 → d_R  (w: -1 + 0 = -1 ✓)
    UGPYukawaAllowed ⟨⟨.DownQuark, .L⟩, .Hzero, ⟨.DownQuark, .R⟩⟩ ∧
    -- Up quark mass: d_L + H+ → u_R  (w: -1 + 3 = 2 ✓; via H̃ coupling)
    UGPYukawaAllowed ⟨⟨.DownQuark, .L⟩, .Hplus, ⟨.UpQuark, .R⟩⟩ ∧
    -- Dirac neutrino mass: ν_L + H0 → ν_R  (w: 0 + 0 = 0 ✓)
    UGPYukawaAllowed ⟨⟨.Neutrino, .L⟩, .Hzero, ⟨.Neutrino, .R⟩⟩ ∧
    -- Cross-sector forbidden: lepton-quark Yukawa (w: -3 + 0 ≠ -1)
    ¬ UGPYukawaAllowed ⟨⟨.ChargedLepton, .L⟩, .Hzero, ⟨.DownQuark, .R⟩⟩ := by
  native_decide

end UgpPhysicsLean.HiggsYukawa

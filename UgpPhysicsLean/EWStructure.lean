import Mathlib
import UgpLean.BraidAtlas.ChargeTheorem
import UgpLean.GTE.FiberBundle
import UgpPhysicsLean.BraidAtlas.Cobordism

/-!
# UgpPhysicsLean.EWStructure — Full Electroweak Quantum-Number Reconstruction

**Specs:** 017-09, 017-10, 017-11, 017-12 — Epic 17B
**Status:** Zero sorry

## Integerization: T₆ + Y₃ = 2W (all integers, no fractions)
-/

namespace UgpPhysicsLean.EWStructure

open UgpLean.BraidAtlas UgpLean.GTE UgpPhysicsLean.BraidAtlas

-- ════════════════════════════════════════════════════════════════
-- §0  Finite type infrastructure
-- ════════════════════════════════════════════════════════════════

inductive Chirality : Type where | L | R
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Chirality := ⟨{.L, .R}, by intro c; cases c <;> simp⟩

-- Simp lemmas for Chirality distinctness (needed for simp_all to detect contradictions)
@[simp] private theorem chi_L_ne_R : ¬ (Chirality.L = Chirality.R) := by decide
@[simp] private theorem chi_R_ne_L : ¬ (Chirality.R = Chirality.L) := by decide

-- Fintype for SMFermionType (already in ugp-lean; adding here for ChiralFermion)
instance : Fintype SMFermionType :=
  ⟨{.ChargedLepton, .Neutrino, .UpQuark, .DownQuark}, by intro x; cases x <;> simp⟩

structure ChiralFermion where
  fermionType : SMFermionType
  chirality   : Chirality
  deriving DecidableEq, Repr

instance : Fintype ChiralFermion :=
  Fintype.ofEquiv (SMFermionType × Chirality)
    { toFun    := fun p => ⟨p.1, p.2⟩
      invFun   := fun c => (c.fermionType, c.chirality)
      left_inv  := fun _ => rfl
      right_inv := fun _ => rfl }

-- ════════════════════════════════════════════════════════════════
-- §1  Spec 017-09 — Hypercharge [T]
-- ════════════════════════════════════════════════════════════════

/-- T₆ = 6·T₃: ±3 for left-handed doublet members; 0 for right-handed singlets. -/
def T6 (f : ChiralFermion) : ℤ :=
  match f.chirality with
  | .R => 0
  | .L => match f.fermionType with
    | .ChargedLepton => -3  | .Neutrino => 3
    | .UpQuark       =>  3  | .DownQuark => -3

/-- Y₃ = 2W − T₆ (hypercharge ×3, from UGP winding). -/
def Y3 (f : ChiralFermion) : ℤ :=
  2 * windingNumber 3 f.fermionType - T6 f

/-- **017-09 [T]: T₆ + Y₃ = 2W** -/
theorem ew_charge_formula_integer (f : ChiralFermion) :
    T6 f + Y3 f = 2 * windingNumber 3 f.fermionType := by simp [Y3]

/-- **017-09 [T]: SM hypercharge table recovered** -/
theorem sm_hypercharge_table_recovered :
    Y3 ⟨.Neutrino,      .L⟩ = -3 ∧ Y3 ⟨.ChargedLepton, .L⟩ = -3 ∧
    Y3 ⟨.UpQuark,       .L⟩ =  1 ∧ Y3 ⟨.DownQuark,     .L⟩ =  1 ∧
    Y3 ⟨.ChargedLepton, .R⟩ = -6 ∧ Y3 ⟨.UpQuark,       .R⟩ =  4 ∧
    Y3 ⟨.DownQuark,     .R⟩ = -2 := by simp [Y3, T6, windingNumber]

-- ════════════════════════════════════════════════════════════════
-- §2  Spec 017-10 — Chirality [T]
-- ════════════════════════════════════════════════════════════════

def isWeakDoubletMember (f : ChiralFermion) : Bool :=
  match f.chirality with | .L => true | .R => false

def weakPartner (f : ChiralFermion) : Option ChiralFermion :=
  match f.chirality with
  | .R => none
  | .L => match f.fermionType with
    | .ChargedLepton => some ⟨.Neutrino,      .L⟩
    | .Neutrino      => some ⟨.ChargedLepton, .L⟩
    | .UpQuark       => some ⟨.DownQuark,     .L⟩
    | .DownQuark     => some ⟨.UpQuark,       .L⟩

/-- **017-10 [T]: Only left-handed fermions have weak partners.** -/
theorem only_left_chiral_have_weak_partners (f : ChiralFermion) :
    (weakPartner f).isSome ↔ f.chirality = .L := by
  obtain ⟨ft, chi⟩ := f; cases chi <;> cases ft <;> simp [weakPartner]

/-- **017-10 [T]: Right-chiral fermions are weak singlets (T₆ = 0).** -/
theorem right_chiral_are_weak_singlets (f : ChiralFermion) (h : f.chirality = .R) :
    T6 f = 0 := by
  obtain ⟨ft, chi⟩ := f
  cases chi <;> cases ft <;> simp_all [T6]

/-- **017-10 [T]: Left-chiral fermions have T₆ ≠ 0.** -/
theorem left_chiral_have_nonzero_T6 (f : ChiralFermion) (h : f.chirality = .L) :
    T6 f ≠ 0 := by
  obtain ⟨ft, chi⟩ := f
  cases chi <;> cases ft <;> simp_all [T6]

/-- **017-10 [T]: Doublet partners always left-handed.** -/
theorem doublet_partner_is_left_chiral (f : ChiralFermion)
    (h : f.chirality = .L) (p : ChiralFermion) (hp : weakPartner f = some p) :
    p.chirality = .L := by
  have key : ∀ f p : ChiralFermion,
      f.chirality = .L → weakPartner f = some p → p.chirality = .L := by
    native_decide
  exact key f p h hp

-- ════════════════════════════════════════════════════════════════
-- §3  Spec 017-11 — Gauge-boson winding spectrum [T]
-- ════════════════════════════════════════════════════════════════

inductive EWBoson : Type where
  | photon | Z | Wplus | Wminus  deriving DecidableEq, Repr

instance : Fintype EWBoson :=
  ⟨{.photon, .Z, .Wplus, .Wminus}, by intro b; cases b <;> simp⟩

def bosonWinding : EWBoson → ℤ
  | .photon => 0 | .Z => 0 | .Wplus => 3 | .Wminus => -3

/-- **017-11 [T]: EW boson winding spectrum ⊆ {0, ±3}.** -/
theorem ew_boson_winding_in_spectrum (B : EWBoson) :
    bosonWinding B ∈ ({0, 3, -3} : Finset ℤ) := by
  cases B <;> simp [bosonWinding]

/-- Winding-conserving EW vertex: W(f₁) = W(f₂) + W(B). -/
def UGPAllowsEWVertex (f1 f2 : ChiralFermion) (B : EWBoson) : Prop :=
  windingNumber 3 f1.fermionType = windingNumber 3 f2.fermionType + bosonWinding B

/-- **017-11 [T]: EW vertex → |ΔW| ∈ {0, 3}.** -/
theorem ew_vertex_implies_standard_winding (f1 f2 : ChiralFermion) (B : EWBoson)
    (h : UGPAllowsEWVertex f1 f2 B) :
    Int.natAbs (windingNumber 3 f1.fermionType - windingNumber 3 f2.fermionType) = 0 ∨
    Int.natAbs (windingNumber 3 f1.fermionType - windingNumber 3 f2.fermionType) = 3 := by
  obtain ⟨ft1, _⟩ := f1; obtain ⟨ft2, _⟩ := f2
  cases B <;> cases ft1 <;> cases ft2 <;>
    simp_all [UGPAllowsEWVertex, bosonWinding, windingNumber]

/-- **017-11 [T]: SM-standard transitions have an EW boson mediator.** -/
theorem sm_transition_has_ew_boson (f1 f2 : ChiralFermion)
    (h : f1.fermionType = f2.fermionType ∨
         UGPWeakPair f1.fermionType f2.fermionType = true) :
    ∃ B : EWBoson, UGPAllowsEWVertex f1 f2 B := by
  obtain ⟨ft1, _⟩ := f1; obtain ⟨ft2, _⟩ := f2
  simp only [UGPAllowsEWVertex]
  rcases h with rfl | hW
  · exact ⟨.photon, by simp [bosonWinding]⟩
  · cases ft1 <;> cases ft2 <;>
      simp_all [UGPWeakPair, sameSector, isLepton, isQuark, windingNumber] <;>
      first
      | exact ⟨.Wminus, by decide⟩
      | exact ⟨.Wplus,  by decide⟩

/-- **017-11 [T]: Exotic winding → no SM EW boson.** -/
theorem exotic_winding_no_ew_boson (f1 f2 : ChiralFermion)
    (hex : Int.natAbs (windingNumber 3 f1.fermionType -
                       windingNumber 3 f2.fermionType) ∈ ({1, 2, 5} : Finset ℕ)) :
    ¬ ∃ B : EWBoson, UGPAllowsEWVertex f1 f2 B := by
  obtain ⟨ft1, _⟩ := f1; obtain ⟨ft2, _⟩ := f2
  intro ⟨B, hB⟩
  cases ft1 <;> cases ft2 <;>
    simp_all [windingNumber, UGPAllowsEWVertex] <;>
    cases B <;> simp_all [bosonWinding]

/-- **017-11 [T]: EW vertex biconditional.** -/
theorem ew_vertex_iff_sm_standard (f1 f2 : ChiralFermion) :
    (∃ B : EWBoson, UGPAllowsEWVertex f1 f2 B) ↔
    (f1.fermionType = f2.fermionType ∨
     UGPWeakPair f1.fermionType f2.fermionType = true) := by
  constructor
  · rintro ⟨B, hB⟩
    rcases ew_vertex_implies_standard_winding f1 f2 B hB with h0 | h3
    · left;  exact (ugp_neutral_pair_iff_same_type f1.fermionType f2.fermionType).mp h0
    · right
      obtain ⟨ft1, _⟩ := f1; obtain ⟨ft2, _⟩ := f2
      cases ft1 <;> cases ft2 <;>
        simp_all [windingNumber, UGPWeakPair, sameSector, isLepton, isQuark]
  · exact sm_transition_has_ew_boson f1 f2

-- ════════════════════════════════════════════════════════════════
-- §4  Spec 017-12 — Full anomaly cancellation [T]
-- ════════════════════════════════════════════════════════════════

/-- [grav]²U(1)_Y per generation: Σ Y₃(L) − Σ Y₃(R). -/
def perGenGravAnom : ℤ :=
  Y3 ⟨.Neutrino, .L⟩ + Y3 ⟨.ChargedLepton, .L⟩ +
  3 * (Y3 ⟨.UpQuark, .L⟩ + Y3 ⟨.DownQuark, .L⟩) -
  Y3 ⟨.ChargedLepton, .R⟩ -
  3 * (Y3 ⟨.UpQuark, .R⟩ + Y3 ⟨.DownQuark, .R⟩)

/-- **017-12 [T]: [grav]²U(1)_Y = 0** -/
theorem anomaly_grav_cancel : perGenGravAnom = 0 := by
  simp only [perGenGravAnom, Y3, T6, windingNumber]; norm_num

/-- [SU(2)]²U(1)_Y: Σ Y₃ over left-handed doublet members. -/
def su2GaugeAnom : ℤ :=
  Y3 ⟨.Neutrino, .L⟩ + Y3 ⟨.ChargedLepton, .L⟩ +
  3 * (Y3 ⟨.UpQuark, .L⟩ + Y3 ⟨.DownQuark, .L⟩)

/-- **017-12 [T]: [SU(2)]²U(1)_Y = 0** -/
theorem anomaly_su2_cancel : su2GaugeAnom = 0 := by
  simp only [su2GaugeAnom, Y3, T6, windingNumber]; norm_num

/-- [SU(3)]²U(1)_Y: Σ Y₃(L quarks) − Σ Y₃(R quarks). -/
def su3GaugeAnom : ℤ :=
  (Y3 ⟨.UpQuark, .L⟩ + Y3 ⟨.DownQuark, .L⟩) -
  (Y3 ⟨.UpQuark, .R⟩ + Y3 ⟨.DownQuark, .R⟩)

/-- **017-12 [T]: [SU(3)]²U(1)_Y = 0** -/
theorem anomaly_su3_cancel : su3GaugeAnom = 0 := by
  simp only [su3GaugeAnom, Y3, T6, windingNumber]; norm_num

/-- [U(1)_Y]³ per generation. -/
def cubicY3Anom : ℤ :=
  (Y3 ⟨.Neutrino, .L⟩)^3 + (Y3 ⟨.ChargedLepton, .L⟩)^3 +
  3 * ((Y3 ⟨.UpQuark, .L⟩)^3 + (Y3 ⟨.DownQuark, .L⟩)^3) -
  (Y3 ⟨.ChargedLepton, .R⟩)^3 -
  3 * ((Y3 ⟨.UpQuark, .R⟩)^3 + (Y3 ⟨.DownQuark, .R⟩)^3)

/-- **017-12 [T]: [U(1)_Y]³ = 0** -/
theorem anomaly_cubic_cancel : cubicY3Anom = 0 := by
  simp only [cubicY3Anom, Y3, T6, windingNumber]; norm_num

/-- **017-12 Summary [T]: All four SM gauge anomalies cancel.** -/
theorem all_four_sm_anomalies_cancel :
    perGenGravAnom = 0 ∧ su2GaugeAnom = 0 ∧ su3GaugeAnom = 0 ∧ cubicY3Anom = 0 :=
  ⟨anomaly_grav_cancel, anomaly_su2_cancel, anomaly_su3_cancel, anomaly_cubic_cancel⟩

end UgpPhysicsLean.EWStructure

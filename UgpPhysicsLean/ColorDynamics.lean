import Mathlib
import UgpLean.BraidAtlas.ChargeTheorem
import UgpPhysicsLean.EWStructure

/-!
# UgpPhysicsLean.ColorDynamics — Color Fiber and Gluon Theorem

**Spec:** 017-13 — Color fiber and gluon adjoint theorem
**Epic:** 17B — UGP Dynamics Closure
**Status:** Zero sorry

## Key theorems

- `gluon_vertices_quarks_only [T]`: gluons only couple to quarks
- `gluon_preserves_winding [T]`: strong vertex has ΔW = 0
- `no_lepton_gluon_coupling [T]`: leptons are color-neutral
- `gluon_color_change_not_em [T]`: color-changing vertex ≠ EM vertex
- `baryon_rgb_satisfies_conditions [T]`: rgb triple has distinct colors
-/

namespace UgpPhysicsLean.ColorDynamics

open UgpLean.BraidAtlas UgpLean.GTE
open UgpPhysicsLean.BraidAtlas (isLepton isQuark)
open UgpPhysicsLean.EWStructure

-- ════════════════════════════════════════════════════════════════
-- §1  Color types
-- ════════════════════════════════════════════════════════════════

inductive Color : Type where
  | red | green | blue  deriving DecidableEq, Repr

instance : Fintype Color := ⟨{.red, .green, .blue}, by intro c; cases c <;> simp⟩

/-- Coloured fermion: flat structure (fermionType + chirality + optional color). -/
structure ColoredFermion where
  fermionType : SMFermionType
  chirality   : Chirality
  color       : Option Color
  deriving DecidableEq, Repr

/-- Construct a ColoredFermion from a ChiralFermion with an explicit colour. -/
def ColoredFermion.ofChiral (f : ChiralFermion) (c : Option Color) : ColoredFermion :=
  { fermionType := f.fermionType, chirality := f.chirality, color := c }

-- ════════════════════════════════════════════════════════════════
-- §2  Gluon type
-- ════════════════════════════════════════════════════════════════

/-- A gluon: carries a colour-in and colour-out index.
The 8 SU(3) generators correspond to the 8 non-trivial (colorIn, colorOut) pairs
(off-diagonal: 6; diagonal Cartan: 2). -/
structure Gluon where
  colorIn  : Color
  colorOut : Color
  deriving DecidableEq, Repr

/-- A strong QCD vertex: q(c_in) → q(c_out) + gluon(c_in → c_out). -/
def StrongVertex (qIn qOut : ColoredFermion) (g : Gluon) : Prop :=
  qIn.fermionType = qOut.fermionType ∧   -- flavor preserved
  isQuark qIn.fermionType = true       ∧  -- quarks only
  qIn.color = some g.colorIn           ∧  -- incoming color matches gluon
  qOut.color = some g.colorOut            -- outgoing color matches gluon

/-- EM vertex: same fermion type, same color. -/
def EMVertex (qIn qOut : ColoredFermion) : Prop :=
  qIn.fermionType = qOut.fermionType ∧ qIn.color = qOut.color

-- ════════════════════════════════════════════════════════════════
-- §3  Key theorems [T]
-- ════════════════════════════════════════════════════════════════

/-- **017-13 [T]: Gluon vertices involve quarks only.** -/
theorem gluon_vertices_quarks_only (qIn qOut : ColoredFermion) (g : Gluon)
    (h : StrongVertex qIn qOut g) :
    isQuark qIn.fermionType = true ∧ isQuark qOut.fermionType = true := by
  obtain ⟨hflavor, hquark, _, _⟩ := h
  exact ⟨hquark, hflavor ▸ hquark⟩

/-- **017-13 [T]: Gluon preserves winding (ΔW = 0 for strong vertex).** -/
theorem gluon_preserves_winding (qIn qOut : ColoredFermion) (g : Gluon)
    (h : StrongVertex qIn qOut g) :
    windingNumber 3 qIn.fermionType = windingNumber 3 qOut.fermionType :=
  congrArg (windingNumber 3) h.1

/-- **017-13 [T]: Same fermion type (flavor) in gluon vertex.** -/
theorem gluon_same_flavor (qIn qOut : ColoredFermion) (g : Gluon)
    (h : StrongVertex qIn qOut g) :
    qIn.fermionType = qOut.fermionType := h.1

/-- Lepton and quark classes are mutually exclusive. -/
private lemma isLepton_not_isQuark (ft : SMFermionType) :
    isLepton ft = true → isQuark ft = true → False := by
  cases ft <;> simp [isLepton, isQuark]

/-- **017-13 [T]: Leptons have no colour — no gluon coupling.** -/
theorem no_lepton_gluon_coupling (l : ColoredFermion) (g : Gluon)
    (hl : isLepton l.fermionType = true) :
    ∀ q : ColoredFermion, ¬ StrongVertex l q g ∧ ¬ StrongVertex q l g := by
  intro q
  refine ⟨fun ⟨_, hquark_l, _, _⟩ => ?_, fun ⟨hflavor, hquark_q, _, _⟩ => ?_⟩
  · -- l is lepton AND quark: contradiction
    exact isLepton_not_isQuark _ hl hquark_l
  · -- q.fermionType = l.fermionType; l is lepton; so q must be lepton too
    -- but hquark_q says q is quark: contradiction
    rw [← hflavor] at hl
    exact isLepton_not_isQuark _ hl hquark_q

/-- **017-13 [T]: EM vertex preserves colour.** -/
theorem em_preserves_color (qIn qOut : ColoredFermion) (h : EMVertex qIn qOut) :
    qIn.color = qOut.color := h.2

/-- **017-13 [T]: A colour-changing gluon vertex is NOT an EM vertex.** -/
theorem gluon_color_change_not_em (qIn qOut : ColoredFermion) (g : Gluon)
    (h : StrongVertex qIn qOut g) (hc : g.colorIn ≠ g.colorOut) :
    ¬ EMVertex qIn qOut := by
  intro ⟨_, hcolor⟩
  obtain ⟨_, _, hcIn, hcOut⟩ := h
  rw [hcIn, hcOut] at hcolor
  exact hc (Option.some.inj hcolor)

-- ════════════════════════════════════════════════════════════════
-- §4  Colour singlets
-- ════════════════════════════════════════════════════════════════

/-- Meson: quark + (same-colour anti)quark. -/
def IsMesonPair (q qbar : ColoredFermion) : Prop :=
  isQuark q.fermionType = true ∧ isQuark qbar.fermionType = true ∧
  q.color = qbar.color

/-- Baryon: one of each colour. -/
def IsBaryon (q1 q2 q3 : ColoredFermion) : Prop :=
  isQuark q1.fermionType = true ∧ isQuark q2.fermionType = true ∧
  isQuark q3.fermionType = true ∧
  q1.color = some .red ∧ q2.color = some .green ∧ q3.color = some .blue

/-- **017-13 [T]: Baryon rgb triple has all different colours.** -/
theorem baryon_rgb_all_distinct (q1 q2 q3 : ColoredFermion)
    (h : IsBaryon q1 q2 q3) :
    q1.color ≠ q2.color ∧ q2.color ≠ q3.color ∧ q1.color ≠ q3.color := by
  obtain ⟨_, _, _, hc1, hc2, hc3⟩ := h
  rw [hc1, hc2, hc3]
  exact ⟨by decide, by decide, by decide⟩

end UgpPhysicsLean.ColorDynamics

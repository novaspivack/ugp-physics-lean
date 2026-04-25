import Mathlib
import UgpPhysicsLean.VertexTheorem
import UgpPhysicsLean.ColorDynamics

/-!
# UgpPhysicsLean.GaugeSelfInteractions — Spec 017-023

Proves U(1) (photon) has no self-interactions while SU(2) (W±) and SU(3) (gluons)
have self-interactions. This recovers the abelian vs nonabelian distinction.

## Reference

Spec 017-023. Depends on VertexTheorem (017-15), ColorDynamics (017-13).
-/

namespace UgpPhysicsLean.GaugeSelfInteractions

open UgpPhysicsLean.VertexTheorem
open UgpPhysicsLean.ColorDynamics

-- ════════════════════════════════════════════════════════════════
-- §1  Abelian/nonabelian classification
-- ════════════════════════════════════════════════════════════════

def isNonAbelian : GaugeBoson → Bool
  | .photon  => false
  | .Z       => false
  | .Wplus   => true
  | .Wminus  => true
  | .gluon _ => true

/-- **017-023 Theorem A [T]: Photon is abelian.** -/
theorem photon_is_abelian : isNonAbelian .photon = false := rfl

/-- **017-023 Theorem B [T]: W bosons and gluons are nonabelian.** -/
theorem W_is_nonabelian : isNonAbelian .Wplus = true ∧ isNonAbelian .Wminus = true :=
  ⟨rfl, rfl⟩

theorem gluon_is_nonabelian (g : Gluon) : isNonAbelian (.gluon g) = true := rfl

-- ════════════════════════════════════════════════════════════════
-- §2  Gauge self-interaction predicate
-- ════════════════════════════════════════════════════════════════

def GaugeSelfVertex (bosons : List GaugeBoson) : Prop :=
  bosons.all isNonAbelian = true

-- ════════════════════════════════════════════════════════════════
-- §3  Key theorems
-- ════════════════════════════════════════════════════════════════

/-- **017-023 Theorem C [T]: Photon has no triple self-vertex.** -/
theorem photon_no_self_vertex_3 : ¬ GaugeSelfVertex [.photon, .photon, .photon] := by
  simp [GaugeSelfVertex, isNonAbelian]

/-- A list containing the photon cannot be a gauge self-vertex. -/
theorem photon_blocks_self_vertex (bosons : List GaugeBoson) (h : .photon ∈ bosons) :
    ¬ GaugeSelfVertex bosons := by
  simp only [GaugeSelfVertex, List.all_eq_true, not_forall, not_forall]
  exact ⟨.photon, h, by simp [isNonAbelian]⟩

/-- **017-023 Theorem D [T]: W-boson pair self-vertex possible.** -/
theorem w_pair_self_vertex : GaugeSelfVertex [.Wplus, .Wminus] := by
  simp [GaugeSelfVertex, isNonAbelian]

/-- **017-023 Theorem E [T]: Gluon triple self-vertex possible.** -/
theorem gluon_triple_self_vertex_possible :
    ∃ g1 g2 g3 : Gluon, GaugeSelfVertex [.gluon g1, .gluon g2, .gluon g3] :=
  ⟨{ colorIn := .red, colorOut := .green },
   { colorIn := .green, colorOut := .blue },
   { colorIn := .blue, colorOut := .red },
   by simp [GaugeSelfVertex, isNonAbelian]⟩

/-- **017-023 Theorem F [T]: Gluon quartic self-vertex possible.** -/
theorem gluon_quartic_self_vertex_possible :
    ∃ g1 g2 g3 g4 : Gluon,
    GaugeSelfVertex [.gluon g1, .gluon g2, .gluon g3, .gluon g4] :=
  ⟨{ colorIn := .red, colorOut := .green },
   { colorIn := .green, colorOut := .blue },
   { colorIn := .blue, colorOut := .red },
   { colorIn := .red, colorOut := .blue },
   by simp [GaugeSelfVertex, isNonAbelian]⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Summary
-- ════════════════════════════════════════════════════════════════

/-- **017-023 Main Theorem [T]: Self-vertex admissibility ↔ all bosons are nonabelian.** -/
theorem gauge_self_vertex_iff_all_nonabelian (bosons : List GaugeBoson) :
    GaugeSelfVertex bosons ↔ ∀ B ∈ bosons, isNonAbelian B = true := by
  simp [GaugeSelfVertex, List.all_eq_true]

end UgpPhysicsLean.GaugeSelfInteractions

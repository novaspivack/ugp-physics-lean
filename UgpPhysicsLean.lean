-- UgpPhysicsLean — EPIC 17: UGP Dynamics
-- Top-level import file for the ugp-physics-lean library.
--
-- Spec 017-01 (UGP Category) and 017-02 (BraidAtlas.Cobordism) are the
-- Phase 1 targets. Subsequent specs build on them.

import UgpPhysicsLean.UGPCategory
import UgpPhysicsLean.BraidAtlas.Cobordism
import UgpPhysicsLean.EWStructure
import UgpPhysicsLean.ColorDynamics
import UgpPhysicsLean.VertexTheorem
import UgpPhysicsLean.HiggsYukawa
import UgpPhysicsLean.UniquenessTheorems
import UgpPhysicsLean.PSCOrbitCertificate
import UgpPhysicsLean.WindingFromDoublet
import UgpPhysicsLean.PsiBraidFunctor
import UgpPhysicsLean.DiscreteAction
import UgpPhysicsLean.MFRRActionHardening
import UgpPhysicsLean.TopologicalMinimality
import UgpPhysicsLean.ColorConfinement
import UgpPhysicsLean.GaugeSelfInteractions
import UgpPhysicsLean.CategoryEnrichment
import UgpPhysicsLean.ForbiddenProcesses

/-!
# UgpPhysicsLean — Universal Generative Principle: Dynamics Formalization

EPIC 17 formalization. Builds on `ugp-lean` (EPIC 15 prerequisites).

## Module structure

- `UgpPhysicsLean.UGPCategory`         — Spec 017-01: UGP category (C1 skeletal + C2 StableBraidProcess)
- `UgpPhysicsLean.BraidAtlas.Cobordism` — Spec 017-02: Braid cobordism dynamics (C3 conservation + C4 vertices)

## Prerequisites from ugp-lean

- `UgpLean.GTE.FiberBundle`          — EnhancedGTETriple [T]
- `UgpLean.BraidAtlas.ChargeTheorem` — Q = W/N_c [T], winding values [T]
- `UgpLean.GTE.MersenneLadder`       — c₃ = 65535 [T]
- `UgpLean.GTE.ScaleConnection`      — τ-formula ridge morphisms [T]
- `UgpLean.MassRelations.ScaleTransport` — mass ratio Z-independence [T]
- `UgpLean.IPT.InformationProfitThreshold` — IPT = 1 + Λ/2 [T]
-/

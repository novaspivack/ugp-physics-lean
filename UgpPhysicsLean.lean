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
import UgpPhysicsLean.IPT.InformationProfitThreshold
import UgpPhysicsLean.GXT.H9SelfConsistency
import UgpPhysicsLean.GXT.GoldenRatioFixedPoint
import UgpPhysicsLean.NullDiscipline.SaturationBarrier
import UgpPhysicsLean.NullDiscipline.TheoremEligibility
import UgpPhysicsLean.PSC.ThreeRouteForcing

/-!
# UgpPhysicsLean — Universal Generative Principle: Dynamics Formalization

EPIC 17 formalization. Builds on `ugp-lean` (EPIC 15 prerequisites).

## Module structure

- `UgpPhysicsLean.UGPCategory`         — Spec 017-01: UGP category (C1 skeletal + C2 StableBraidProcess)
- `UgpPhysicsLean.BraidAtlas.Cobordism` — Spec 017-02: Braid cobordism dynamics (C3 conservation + C4 vertices)

## New modules (migrated from ugp-lean: broader UGP programme, not gauge physics)

- `UgpPhysicsLean.IPT.InformationProfitThreshold` — IPT = 1 + Λ/2 [T]
- `UgpPhysicsLean.GXT.H9SelfConsistency`          — IPT is unique self-consistent fixed point of T(x)=1/(1−ln2/N) [T]
- `UgpPhysicsLean.GXT.GoldenRatioFixedPoint`      — 1/φ is the unique positive fixed point of x=1/(1+x) [T]
- `UgpPhysicsLean.NullDiscipline.SaturationBarrier`  — Algebraic saturation barrier; URC basis saturated [T]
- `UgpPhysicsLean.NullDiscipline.TheoremEligibility` — Four-gate Theorem-Eligibility Criterion (TEC) [T]
- `UgpPhysicsLean.PSC.ThreeRouteForcing`          — Three-route PSC forcing capstone (conditional, no smuggling) [T]

## Prerequisites from ugp-lean

- `UgpLean.GTE.FiberBundle`          — EnhancedGTETriple [T]
- `UgpLean.BraidAtlas.ChargeTheorem` — Q = W/N_c [T], winding values [T]
- `UgpLean.GTE.MersenneLadder`       — c₃ = 65535 [T]
- `UgpLean.GTE.ScaleConnection`      — τ-formula ridge morphisms [T]
- `UgpLean.MassRelations.ScaleTransport` — mass ratio Z-independence [T]
-/

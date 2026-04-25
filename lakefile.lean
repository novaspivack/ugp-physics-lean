import Lake
open Lake DSL

package «ugp-physics-lean» where
  -- EPIC 17 — UGP Dynamics: Category, Cobordism, and Unified Architecture
  -- Builds on ugp-lean (EPIC 15 prerequisites) and imports Mathlib via shared cache.

-- Local path dependency on ugp-lean.
-- This gives us access to all UgpLean.* modules (GTE.FiberBundle, BraidAtlas.ChargeTheorem, etc.)
-- and reuses ugp-lean's pre-built .lake/build/ artifacts.
require «ugp-lean» from "../ugp-lean"

@[default_target]
lean_lib «UgpPhysicsLean» where
  -- Module structure:
  --   UgpPhysicsLean.UGPCategory      — Spec 017-01: UGP category (C1+C2)
  --   UgpPhysicsLean.BraidAtlas       — Spec 017-02: BraidCobordism (C3+C4)
  --   UgpPhysicsLean.GrandMorphism    — Spec 017-04: PSC ≃ UGP ≃ Braid ≃ SM
  --   UgpPhysicsLean.MFRRAction       — Spec 017-05: MFRR Unified Action

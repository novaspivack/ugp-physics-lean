import Lake
open Lake DSL

package «ugp-physics-lean» where
  -- EPIC 17 — UGP Dynamics: Category, Cobordism, and Unified Architecture
  -- Builds on ugp-lean (EPIC 15 prerequisites) and imports Mathlib via shared cache.

-- Git-pinned dependency on ugp-lean (switched from local path per SPEC_015_LT1 go-live step F).
require «ugp-lean» from git
  "https://github.com/novaspivack/ugp-lean" @ "ed01e6f5b18bcd965b943a765c1b64c446d75a8b"

@[default_target]
lean_lib «UgpPhysicsLean» where
  -- Module structure:
  --   UgpPhysicsLean.UGPCategory      — Spec 017-01: UGP category (C1+C2)
  --   UgpPhysicsLean.BraidAtlas       — Spec 017-02: BraidCobordism (C3+C4)
  --   UgpPhysicsLean.GrandMorphism    — Spec 017-04: PSC ≃ UGP ≃ Braid ≃ SM
  --   UgpPhysicsLean.MFRRAction       — Spec 017-05: MFRR Unified Action

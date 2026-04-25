# ugp-physics-lean

**Lean 4 formalization of the UGP Interaction Skeleton Theorem (EPIC 17)**

This repository contains the Lean 4 proof library accompanying Paper 23:

> **"The UGP Interaction Skeleton Theorem: A Topological-Arithmetic Derivation  
> of the Standard Model's Finite Renormalizable Vertex Structure"**  
> Nova Spivack, April 2026.

## What this proves

All theorems are machine-verified with **zero sorry** for theorem-grade claims.
(One disclosed bridge placeholder in `UGPYukawaWeight`, labeled [B] not [T].)

**Silver closure:**  
`ugp_gauge_fermion_equals_sm` [T] — `UGPVertex(f₁,f₂,B) ↔ SMVertex(f₁,f₂,B)`

**Gold closure:**  
`ugp_yukawa_implies_sm` [T] — UGP Yukawa schemas = SM Yukawa schemas

**Novel predictions:**  
`dark_sector_gap_all_isolated` [T] — W∈{1,−2,4} fermions topologically isolated  
`proton_decay_dim4_forbidden` [T] — dimension-4 proton decay forbidden  
`all_sm_path_zero_action` [T] — SM interaction paths minimize S_UGP = 0

## Dependency

Builds on [`ugp-lean`](https://github.com/novaspivack/ugp-lean) (EPIC 15:
BraidAtlas.ChargeTheorem, GTE.FiberBundle, ScaleTransport, IPT).

## Build

```bash
lake exe cache get   # download Mathlib precompiled cache
lake build           # ~8200 jobs
# Expected: Build completed successfully. 0 errors.
```

## Modules (17)

| Module | Key theorem | Paper § |
|--------|-------------|---------|
| `UGPCategory` | `ugpCategory` [T] | §2 |
| `BraidAtlas.Cobordism` | `sm_allowed_iff_standard_winding_transfer` [T] | §4 |
| `EWStructure` | `sm_hypercharge_table_recovered` [T] | §3 |
| `ColorDynamics` | `gluon_vertices_quarks_only` [T] | §6 |
| `VertexTheorem` | **`ugp_gauge_fermion_equals_sm` [T] (Silver)** | §7 |
| `HiggsYukawa` | **`ugp_yukawa_implies_sm` [T] (Gold)** | §7 |
| `UniquenessTheorems` | `sm_winding_table_uniquely_determined` [T] | §3 |
| `PSCOrbitCertificate` | `canonical_seed_certificate` [T] | §2 |
| `WindingFromDoublet` | `winding_table_two_inputs_suffice` [T] | §3 |
| `PsiBraidFunctor` | `psiBraid_generation_independent` [T] | §2 |
| `DiscreteAction` | `all_sm_path_zero_action` [T] | §9 |
| `MFRRActionHardening` | `pt_as_stationary_condition` [T] | §9 |
| `TopologicalMinimality` | `primitive_cobordisms_are_exactly_sm_gauge_vertices` [T] | §4 |
| `ColorConfinement` | `isolated_quark_not_observable` [T] | §6 |
| `GaugeSelfInteractions` | `gauge_self_vertex_iff_all_nonabelian` [T] | §6 |
| `CategoryEnrichment` | `mirror_involution_squared_is_id` [T] | §2 |
| `ForbiddenProcesses` | `dark_sector_gap_all_isolated` [T] | §8 |

## Companion

Paper 23 PDF and all specs in [ugp-physics](https://github.com/novaspivack/ugp-physics).

Lean version: `v4.29.0-rc6` / Mathlib 4 / MIT License

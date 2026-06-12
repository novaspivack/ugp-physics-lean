# ugp-physics-lean

**General physics Lean 4 library for the UGP program.**

This repository provides formalizations of standard physics that serve as foundations for the GTE/UGP research program. The content here consists of established physics facts — geometry, spacetime structure, spinor representations, and general relativistic infrastructure — that are independent of GTE theory itself.

---

## Research program

This library is part of the UGP Physics research program by [Nova Spivack](https://www.novaspivack.com/).

| Link | Description |
|---|---|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [UGP Physics programme](https://www.novaspivack.com/research/physics-program) | The UGP Physics research programme |
| [Complete GTE Framework](https://doi.org/10.5281/zenodo.20560550) | Paper 48 — the synthesis monograph this library contributes to |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.20644340) | Citable DOI hub for the UGP Physics program |

---

## Separation of concerns

| Repository | What lives here |
|---|---|
| **ugp-physics-lean** (this repo) | Paper 23 (Interaction Skeleton Theorem) dynamics layer — IPT, GXT, NullDiscipline, PSC, and foundational physics facts not specific to GTE |
| [**ugp-lean**](https://github.com/novaspivack/ugp-lean) | GTE/UGP-specific derivations: Z₇ algebra, PSC structure, CMCA dynamics, GTE particle spectrum, MDL initial state, RT formula, fermionic statistics, mass predictions; also hosts Lorentzian/gravity infrastructure (`UgpLean.Gravity`) |

**What belongs here:** Physics facts specific to the UGP Paper 23 dynamics layer — IPT, GXT, NullDiscipline, PSC, and the Interaction Skeleton Theorem proof modules.

**What does NOT belong here:** GTE-specific theorems, and standard Lorentzian/spinor/Wald-entropy infrastructure (those now live in `UgpLean.Gravity`).

**Dependency direction:** ugp-physics-lean imports ugp-lean for GTE prerequisites. The Lorentzian modules (`MinkowskiSpace`, `SpinorRep`, `WaldEntropy`) were moved to `UgpLean.Gravity` in ugp-lean to eliminate the prior cyclic dependency.

---

## Current modules

### Standard physics infrastructure

| Module | Contents |
|---|---|
| `NullDiscipline/SaturationBarrier.lean` | Null structure and saturation barrier |
| `NullDiscipline/TheoremEligibility.lean` | Null discipline for theorem eligibility |
| `GXT/AsymptoticSparsity.lean` | Asymptotic sparsity of GXT structures |
| `GXT/GoldenRatioFixedPoint.lean` | Golden ratio fixed-point structure |
| `GXT/H9Attractivity.lean` | H9 attractor analysis |
| `GXT/H9SelfConsistency.lean` | H9 self-consistency |
| `GXT/LieExpSurjective.lean` | Surjectivity of the Lie exponential map |
| `GXT/U1DirectProof.lean` | Direct proof of U(1) structure |
| `IPT/InformationProfitThreshold.lean` | Information profit threshold |
| `PSC/ThreeRouteForcing.lean` | Three-route forcing for Planck seed candidates |
| `BraidAtlas/Cobordism.lean` | Braid atlas cobordism structure |

> **Note:** The Lorentzian infrastructure (`MinkowskiSpace`, `SpinorRep`, `WaldEntropy`) was moved to `UgpLean.Gravity` in [ugp-lean](https://github.com/novaspivack/ugp-lean) to eliminate the cyclic Lake dependency that previously existed between the two repos. These modules are now at `UgpLean.Gravity.MinkowskiSpace`, `UgpLean.Gravity.SpinorRep`, and `UgpLean.Gravity.WaldEntropy`.

### Paper 23 — Interaction Skeleton Theorem (17 modules)

This repository also contains the Lean 4 proof library for Paper 23:

> **"The UGP Interaction Skeleton Theorem: A Topological-Arithmetic Derivation  
> of the Standard Model's Finite Renormalizable Vertex Structure"**  
> Nova Spivack, April 2026.

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

---

## Dependencies

Builds on [`ugp-lean`](https://github.com/novaspivack/ugp-lean) (EPIC 15:
BraidAtlas.ChargeTheorem, GTE.FiberBundle, ScaleTransport, IPT).

---

## Build

```bash
lake exe cache get   # download Mathlib precompiled cache
lake build           # ~8200 jobs
# Expected: Build completed successfully. 0 errors.
```

---

## Companion

Paper 23 PDF and all specs in [ugp-physics](https://github.com/novaspivack/ugp-physics).  
GTE/UGP-specific Lean formalizations: [ugp-lean](https://github.com/novaspivack/ugp-lean).

Lean version: `v4.29.0-rc6` / Mathlib v4.29.1 / MIT License

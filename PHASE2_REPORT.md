# Experiment 004 — Phase 2 verification report

Date: 2026-11-09

**COMPLETE: the exact original `FullTarget` is kernel-checked.** There are no outstanding proof obligations for that target.

```lean
theorem Zagreb004.fullTarget : Zagreb004.FullTarget :=
  ⟨Zagreb004.exists46, Zagreb004.minimality,
    Zagreb004.all_orders, Zagreb004.extremal_classification⟩
```

The theorem has no additional hypotheses. This report supersedes the historical incomplete status in the original README, verification reports and Phase 1 report. Original research documents and historical audit records remain preserved.

## Exact final verification results

Environment: Ubuntu 24.04.5 / WSL2, Lean 4.19.0, Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

`lake build` exited **0**, without errors or warnings:

```text
✔ [6660/6664] Built Zagreb004.Family
✔ [6661/6664] Built Zagreb004.Cores
✔ [6662/6664] Built Zagreb004.Full
✔ [6663/6664] Built Zagreb004
Build completed successfully.
```

GraphCounting and GraphTheorems had compiled successfully earlier and their current outputs were reused. The final build compiled the complete project import graph, including Full.

`lake env lean Audit.lean` exited **0**, without errors or warnings. It audited **90 public theorems**, including every new public Phase 2 theorem, and printed the original target definitions and the final proof term. The decisive output was:

```text
'Zagreb004.fullTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
Zagreb004.all_orders : Zagreb004.AllOrdersTarget
Zagreb004.fullTarget : Zagreb004.FullTarget
```

All 90 theorem axiom sets are subsets of those three standard Lean axioms. There is no `sorryAx`, unproved custom axiom, or native-evaluation axiom dependency. The source policy scan passed on all project Lean files. Finite certificates use `decide +kernel`; the unbounded family is proved symbolically, not tested at finitely many orders.

Dependency-pin validation passed again. The original `Definitions.lean`, `Targets.lean`, all Phase 1 proof modules, `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are byte-for-byte unchanged against the Phase 2 baseline. In particular, the original graph-theoretic hypotheses were not weakened or replaced by profile assumptions.

## Completed proof chain

| Obligation | Kernel-checked declarations |
| --- | --- |
| Weighted incidence for arbitrary finite graphs | `weighted_incidence`, `degree_incidence` |
| Ten degree-pair types exhaust all edges under degrees 2–5 | `edge_profile_sum`, `profile_size` |
| Actual graph order and Zagreb index formulas | `profile_order`, `profile_first`, `profile_second` |
| Four incidence equations | `incidence2`, `incidence3`, `incidence4`, `incidence5` |
| Universal quadratic graph-gap identity | `graph_gap_identity`, `positive_gap_profile` |
| Necessary cut conditions from connectedness | `connected_crossing`, `profile_cuts` |
| Graph-to-profile classification at order at most 46 | `small_counterexample_profile` |
| No qualifying counterexample below order 46 | `minimality : MinimalityTarget` |
| Every qualifying order-46 counterexample has the canonical profile | `extremal_classification : ExtremalProfileTarget` |
| Concrete order-46 existence | `exists46 : Exists46Target`, using the Phase 1 witness |
| Actual counterexamples at every order at least 46 | `even_order_counterexample`, `odd_order_counterexample`, `all_orders : AllOrdersTarget` |
| All original targets together | `fullTarget : FullTarget` |

### Graph counting and minimality

The counting lemmas begin with the actual `SimpleGraph (Fin n)` and its actual adjacency relation. `weighted_incidence` counts each endpoint of every increasing ordered edge pair once. `edge_profile_sum` partitions these edges by the minimum and maximum endpoint degrees; this proves an identity for every symmetric rational edge weight.

Weights 1, the product of endpoint degrees, their sum, and the sum of their reciprocal degrees scaled by 60 yield the edge count, second Zagreb index, first Zagreb index, and vertex count. Indicator weights give the four degree-incidence equations.

The quadratic profile identity from Phase 1 is then transferred to the graph's actual integer gap. Connectedness supplies an edge across every nontrivial vertex cut. The degree-3 cut and the {2,5} cut establish the two profile cut conditions, rather than assuming them.

These facts discharge every hypothesis of the existing profile classification. A counterexample of order at most 46 therefore has profile

```text
(e22,e23,e24,e25,e33,e34,e35,e44,e45,e55)
= (0,1,0,35,31,0,0,0,0,0).
```

Its `order60` is 2760, forcing order 46 and excluding every order at most 45. The same classification proves the exact original extremal-profile target.

### Infinite family of actual graphs

The construction uses two fixed simple graph cores, with five or seven hubs. Each core comes from a doubled hub cycle and a matching, subdividing each edge copy with its own distinct vertex and adding a pendant attachment vertex. The fixed cores have 18 and 25 vertices respectively. Their connectivity, vertexwise adjusted degree tables, edge-degree properties, and counts are kernel-checked finite certificates in `Cores.lean`.

For arbitrary `t : Nat`, `Family.component t` is a prism with two cycles of length `t+3`, with the rung at zero subdivided by a new vertex. The component is proved connected; the new vertex has degree 2 and every other component vertex has degree 3. A generic bridge operation joins the core pendant to this subdivision vertex. Its connectedness and exact degree changes are proved generally. A finite equivalence transports the resulting simple graph to `Fin n`, preserving adjacency and degrees.

This is a valid variant of the research construction: it subdivides a prism **rung** rather than a cycle edge. The proof verifies the necessary graph properties and gap for this variant directly; it does not assume that the two choices are isomorphic.

- For even `n >= 46`, use the seven-hub core and `t = (n-32)/2`. The cycle length is `(n-26)/2`, and the assembled graph has exactly n vertices, 18 degree-2 vertices and 7 degree-5 vertices.
- For odd `n >= 47`, use the five-hub core and `t = (n-25)/2`. The cycle length is `(n-19)/2`, and the assembled graph has exactly n vertices, 13 degree-2 vertices and 5 degree-5 vertices.

Every remaining vertex has degree 3. All edge types are among (2,5), (3,3), and (2,3). The verified incidence equations and degree counts determine the relevant profile entries, and the universal graph-gap identity proves a strictly positive gap in both parity cases. Since order and edge count are positive, this is equivalent to the original strict normalized Zagreb inequality violation. Both extrema are explicitly attained and connectedness is proved.

Only the five-hub and seven-hub families are needed for `AllOrdersTarget`; no assertion about an arbitrary odd number of hubs is required or assumed.

## Files and preservation

Added:

- `Zagreb004/GraphCounting.lean`: graph counting, universal gap and connectedness cuts.
- `Zagreb004/GraphTheorems.lean`: exact minimality and extremal targets.
- `Zagreb004/Family.lean`: generic component, bridge, transport, degree counts and family gap proofs.
- `Zagreb004/Cores.lean`: kernel-checked fixed-core certificates.
- `Zagreb004/Full.lean`: both parity families, all-orders existence and the exact FullTarget theorem.
- `audit/phase2_verification_status.json` and this report.

Updated the root import module, expanded `Audit.lean`, and added a current-status banner to README while retaining its historical contents. The original research PDF, original verification ZIP and verification PDF match the hashes recorded in Phase 1. The historical reports, target definitions and Phase 1 sources were not rewritten.

A baseline snapshot, complete Lean-source patch, diagnostic compiler logs, final source hashes and validation records are stored under `local-logs/phase2/`. This directory remains ignored by the pre-existing .gitignore; retain it when sharing raw verification evidence.

## Evidence

- [Final build output](local-logs/phase2/build-final.txt)
- [Complete final axiom and statement audit](local-logs/phase2/audit-final.txt)
- [Static scan](local-logs/phase2/static-scan.json)
- [Validated dependency pins](local-logs/phase2/pins.txt)
- [Original statement/configuration comparison](local-logs/phase2/original-statements-unchanged.json)
- [Research artifact hashes](local-logs/phase2/research-artifacts.txt)
- [Source changes](local-logs/phase2/source-changes.patch)
- [Final source checksums](local-logs/phase2/final-sources.sha256)
- [Machine-readable verification status](audit/phase2_verification_status.json)

To reproduce in this configured WSL checkout:

```bash
python3 scripts/check_dependency_pins.py
python3 scripts/audit_sources.py
lake build
lake env lean Audit.lean
```

**Incomplete obligations for the exact FullTarget: none.**

# Experiment 004 — Phase 1 verification report

Date: 2026-11-09

**READY for Phase 2.** All existing candidate proofs compile. The full research claim remains incomplete.

This report supersedes the historical uncompiled status for the existing candidate library in README.md, the source headers, VERIFICATION_REPORT.md, and audit/verification_status.json. Those historical records and original research artifacts were preserved. No missing minimality or infinite-family graph proof was implemented in Phase 1.

## Environment and dependency validation

Commands ran in Ubuntu 24.04.5 under WSL2, in `/home/adnan/projects/experiment-004-zagreb-indices`.

- Lean 4.19.0, commit 6caaee842e94; Lake 5.0.0-6caaee8.
- Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `lake exe cache get` cloned the nine dependencies at their pinned revisions and downloaded/unpacked all 6,641 cache files successfully.
- `python3 scripts/check_dependency_pins.py` passed: every checkout HEAD matches the root manifest, the toolchain matches Mathlib, and transitive revisions match Mathlib's own manifest.
- No configuration repair was necessary. `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are byte-for-byte unchanged. No `lake update` was needed.

## Exact final compiler results

`lake build` — exit **0**, no errors or warnings:

```text
✔ [6657/6659] Built Zagreb004.Witness
✔ [6658/6659] Built Zagreb004
Build completed successfully.
```

Definitions, Arithmetic, Profiles and Targets had compiled in the preceding attempts; Lake reused those current outputs. Witness was rebuilt after the final proof correction. All seven project Lean files were compiled across the successful library build and separate audit command.

`lake env lean Audit.lean` — exit **0**, no errors or warnings. It printed axiom dependencies for all **25 public theorems**, followed by the types of the five target proposition definitions. All dependencies are subsets of:

```text
[propext, Classical.choice, Quot.sound]
```

`Arithmetic.all_orders_parameters` uses only `[propext, Quot.sound]`; the other 24 public results use the three axioms above. There is no `sorryAx`, custom axiom, or native evaluation axiom dependency. All 46 private reachability lemmas compiled and are used by the audited connectivity proof. The static source scan also passed with no forbidden tokens (`sorry`, `admit`, custom `axiom`, `native_decide`, or unsafe proof bypasses).

The `#check ...Target` output reports proposition definitions; it does not prove those propositions.

## Changes made

1. **Zagreb004/Arithmetic.lean:** replaced ambiguous `subst a` steps in `patternI_unique` with explicit rewriting by the selected case equality. The old substitution could choose `a = 5*n5` instead of `a = 25`, `35`, or `45`, leaving nonlinear expressions for `omega` and invalidating `rfl`.
2. **Zagreb004/Witness.lean:** corrected the `Connected` constructor for Mathlib's implicit `Nonempty` instance; enabled sequential elaboration; used `decide +kernel`; split the degree table into per-vertex tactic goals; reused the degree table for extrema, indices and edge types; derived the gap from the verified size and indices. This avoids repeated expensive degree calculations and duplicate elaborator reduction. All computation still produces kernel-checked proofs.
3. **Audit.lean:** expanded the audit from selected results to every public candidate theorem, and included the existence target among the proposition-type checks.
4. Added this report and `audit/phase1_verification_status.json`; recorded setup, diagnostics, build results, source diffs and checksums under `local-logs/`.

All **71 existing theorem signatures** (25 public and 46 private), the graph definition and the complete edge list are unchanged. Definitions, Profiles, Targets, the root import module and project configuration are unchanged. The original source/configuration snapshot is in `local-logs/phase1-original-sources.tar.gz`.

Early builds exposed the arithmetic error and high memory use in finite reduction. Three build attempts were stopped intentionally while adjusting proof evaluation; their witness subprocesses exited 143 and the Lake commands exited 1. Temporary diagnostic runs isolated the connectivity constructor error and finite-reduction cost. The diagnostic copy additionally had a documentation-comment error introduced by instrumentation; that copy is not imported by the project. All attempts and outcomes are recorded in `local-logs/phase1-command-results.json`. The final project build and audit both succeeded.

## What is genuinely machine-checked

- **An actual connected simple graph on 46 vertices** exists with degree extrema exactly 2 and 5 and a strict normalized Zagreb inequality violation (`Witness.existence`). The vertex degrees are 5 on vertices 0–6, 2 on 7–24, and 3 on 25–45.
- That graph has **67 edges**, first Zagreb index **436**, second Zagreb index **635**, and integer gap **2**. Its verified edge-type counts include **35** edges of type (2,5), **31** of type (3,3), and **1** of type (2,3).
- The explicit computable degree agrees with Mathlib's degree.
- The coefficient barrier, impossibility of numerical Pattern II, and uniqueness of numerical Pattern I under their stated hypotheses.
- The family arithmetic identities, parity-specific positive-gap formulas, and integer parameter existence for every order at least 46. These are numerical results, not graph realizations.
- The profile gap identity and `Profiles.profile_threshold`: a profile satisfying the stated incidence, cut, order and positive-gap hypotheses equals the canonical profile. Those hypotheses are not yet derived for arbitrary eligible graphs.

## Outstanding Phase 2 proof obligations

1. Prove that the ten actual edge types partition the edges of every eligible graph, and establish the four incidence equations plus the weighted order and Zagreb-index identities.
2. Derive the two profile cut conditions from graph connectedness when the relevant edge counts are positive.
3. Relate positive graph gap to `Profiles.positiveGap` and graph order at most 46 to `order60 <= 2760`. Apply `profile_threshold` to establish **MinimalityTarget** and **ExtremalProfileTarget**.
4. Implement the research report's actual infinite graph family and prove simplicity, connectivity, degree extrema, order, edge counts and Zagreb-index formulas. Combine with the existing parameter lemmas to establish **AllOrdersTarget**.
5. Combine the existing 46-vertex existence proof with the remaining target proofs into **FullTarget**, compile, and audit its axioms.

There are no remaining Phase 1 compiler or dependency blockers. The next Phase 2 action is the general graph-to-profile counting layer; the missing graph proofs have not been started.

## Evidence and reproduction

- [Final library build](local-logs/phase1-build-04.txt)
- [Complete theorem axiom output](local-logs/phase1-audit.txt)
- [Final dependency pin check](local-logs/phase1-pins-final.txt)
- [Static source scan](local-logs/phase1-static-scan.json)
- [All command outcomes](local-logs/phase1-command-results.json)
- [Source patch against the original snapshot](local-logs/phase1-source-changes.patch)
- [Unchanged theorem-signature checks](local-logs/phase1-statements.json)
- [Final source checksums](local-logs/phase1-final-sources.sha256)
- [Original research artifact hash verification](local-logs/phase1-artifacts-verified.txt)
- [Machine-readable current status](audit/phase1_verification_status.json)

`input/research_report.pdf`, `input/original_verification.zip`, and `VERIFICATION_REPORT.pdf` match the hashes recorded before source changes. The original historical logs and reports were not rewritten. `local-logs/` remains ignored by the pre-existing .gitignore; retain it with any handoff requiring the raw build evidence.

To reproduce from this configured checkout:

```bash
python3 scripts/check_dependency_pins.py
python3 scripts/audit_sources.py
lake build
lake env lean Audit.lean
```

A fresh witness compilation uses substantial memory and roughly two minutes on this machine. Incremental builds can reuse its checked output. Do not regenerate the source using the historical generation script without preserving the Phase 1 fixes.

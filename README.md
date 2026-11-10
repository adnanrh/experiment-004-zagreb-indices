# Experiment 004 — Zagreb Indices

An AI-assisted mathematical research experiment directed by a human without formal expertise in this specific mathematical field. The experiment investigates how human prompting, problem formulation, and rigorous machine verification can contribute to mathematical discovery. AI assistance was substantial in mathematical exploration, proof development, Lean implementation, debugging, and documentation.

## Problem and result

For a finite connected simple graph G with n vertices and m edges, define M1 as the sum of squared vertex degrees and M2 as the sum of products of endpoint degrees over edges. The normalized Zagreb inequality is M1/n ≤ M2/m.

[Ali Ghalavand, *On a Conjecture about Comparing the First and Second Zagreb Indices of Graphs*, MATCH 96 (2026), 441–452, Question I, p. 451](https://match.pmf.kg.ac.rs/electronic_versions/Match96/n2/match96n2_441-452.pdf) asks for the threshold for connected simple graphs with minimum degree exactly 2 and maximum degree exactly 5. DOI: [10.46793/match.96-2.04725](https://doi.org/10.46793/match.96-2.04725).

The completed Lean 4 formalization establishes the following for connected simple graphs with minimum degree exactly 2 and maximum degree exactly 5:

- Every qualifying graph with at most **45** vertices satisfies the inequality.
- A qualifying counterexample exists on **46** vertices, so the minimum counterexample order is **46**.
- Every qualifying 46-vertex counterexample has edge-degree counts e23=1, e25=35, e33=31, with all other degree-pair counts zero. This is a profile classification, not a claim of graph-isomorphism uniqueness.
- A qualifying counterexample exists for **every integer order n ≥ 46**.

The concrete 46-vertex witness has 67 edges, M1=436, M2=635 and m*M1−n*M2=2. The exact combined theorem is [`Zagreb004.fullTarget : FullTarget`](Zagreb004/Full.lean); the original statements are in [Targets.lean](Zagreb004/Targets.lean).

## Verification and scope

The final library and axiom audit pass. The proof uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`, `admit`, unproved custom axioms, or native-evaluation proof shortcuts. See the [Phase 2 report](PHASE2_REPORT.md) and [committed verification evidence](verification/).

A fresh adversarial inspection and reproduction checked commit [`68a494573fdbd2e629c620a263dafed5853ac26e`](https://github.com/adnanrh/experiment-004-zagreb-indices/commit/68a494573fdbd2e629c620a263dafed5853ac26e). Successfully executed checks included:

- `lake build` and `lake env lean Audit.lean`, both exiting 0 in the working checkout and an isolated checkout.
- Fresh compilation of all project modules in the isolated checkout, reusing pinned dependency sources and compiled dependency caches. Lean, Mathlib, and the entire toolchain were **not** rebuilt from source.
- Dependency-pin validation, source-policy auditing, and transitive dependency inspection. The final theorem's axiom dependencies were limited to `propext`, `Classical.choice`, and `Quot.sound`.
- All 18 original Python tests and verification of all seven certificates.
- Additional exact-arithmetic checks of the quadratic coefficients and bounded profile search, and checks of actual graph constructions at 259 orders. These finite checks supplement the unbounded Lean proof; optional SymPy and NetworkX cross-checks were not rerun.

This inspection was conducted by the same AI assistant involved in development. It was a fresh adversarial review and reproduction, **not** external mathematical peer review or independent institutional certification. Its additional evidence was retained locally and is not included in the public repository.

Kernel checking establishes correctness relative to the formal definitions and Lean's foundations. The formal audit does **not** verify bibliographic novelty, establish publication priority, or establish the adequacy of every informal exposition. The project director reports that a separate literature investigation supports the originality of the sharp 45/46 threshold and associated extremal results, subject to that investigation's stated limitations. That investigation is not included here; its conclusion is not definitive proof of worldwide priority or independent peer review. External, independent mathematical review of the connection to the published question, definitions, construction, exposition, and related literature remains outstanding. This experiment makes no claim of AI superiority.

## Reproduce

Use Linux or Ubuntu under WSL2 with Git, Python 3, and elan installed. The pinned toolchain is **Lean 4.19.0**; Mathlib is pinned to **c44e0c8ee63ca166450922a373c7409c5d26b00b**. Transitive dependency revisions are recorded in `lake-manifest.json`.

```bash
git clone https://github.com/adnanrh/experiment-004-zagreb-indices.git
cd experiment-004-zagreb-indices
git checkout --detach 68a494573fdbd2e629c620a263dafed5853ac26e
lean --version
lake exe cache get
python3 scripts/check_dependency_pins.py
python3 scripts/audit_sources.py
lake build
lake env lean Audit.lean
```

The first cache command downloads dependencies. Do not change the pinned revisions to bypass a failure. A fresh witness compilation can require several GiB of memory and several minutes. The audit prints axiom dependencies for all 90 public theorems and the exact original target definitions.

Python verification materials and historical outputs are retained in `scripts/`, `logs/`, `audit/`, and `input/original_verification.zip`. They supplement rather than replace Lean verification. Some historical Python checks require SymPy and NetworkX. Do not run `scripts/generate_sources.py` over the completed sources: it is the preserved historical candidate generator and would overwrite later proof repairs.

## Repository guide

- `Zagreb004/`: definitions, witness, arithmetic, profiles, graph counting, minimality, family construction, finite cores and full theorem.
- `Audit.lean`: theorem dependencies and statement audit.
- [Phase 1 report](PHASE1_REPORT.md): verification of the initial candidate library.
- [Phase 2 report](PHASE2_REPORT.md): completed graph-level proof and infinite family. The family subdivides a prism rung; its properties are proved directly.
- `verification/`: compact, publishable build and audit logs; `verification/publication/` records the final pre-push checks.
- `input/`: preserved original research PDF and original Python verification archive.
- `VERIFICATION_REPORT.md`, its PDF, `LOCAL_FORMALIZATION_HANDOFF.md`, `SHA256SUMS`, and older audit files: historical authoring records. Earlier incomplete-status statements are superseded by the completed proof. The existing `SHA256SUMS` is a historical manifest and does not necessarily describe the current working tree; it has not been regenerated.

Detailed local development logs and caches are excluded from Git. Links to `local-logs/` in historical reports refer to local-only records; the relevant successful outputs are preserved under `verification/`.

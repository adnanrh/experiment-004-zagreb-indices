---
title: "Zagreb Threshold: Verification Status"
subtitle: "Experiment 004 — mathematical audit and Lean formalization attempt"
author: "Prepared for Adnan Husain"
date: "9 November 2026"
fontsize: 10pt
geometry: margin=0.8in
mainfont: DejaVu Serif
monofont: DejaVu Sans Mono
colorlinks: true
linkcolor: black
urlcolor: blue
---

## Executive finding

**NOT FORMALLY VERIFIED. No theorem in this package was checked by Lean during this run.**

The supplied mathematical proof and computational artifacts were re-audited. No mathematical error was found in that audit. The original 18 Python test methods passed again, the seven certificates passed a newly written adjacency-matrix verification, and exact coefficient and symbolic polynomial checks agreed with the report.

However, Lean and Lake were not installed in the execution environment. Attempts to obtain an installation failed, including a GitHub request that returned a DNS-resolution error. The compiler and build commands could not launch. Consequently, there are **zero genuinely Lean-checked partial results** from this session.

A pinned **candidate** Lean project has been prepared. It contains an explicit graph witness, an arithmetic profile-classification argument, and family arithmetic. It is uncompiled and may require syntax, API, tactic, or performance repairs. More importantly, the general graph-to-profile reduction and the infinite graph construction have not been formalized. Even if all supplied source files compile elsewhere, that alone will not establish the complete theorem.

### Requested claims and present status

| Claim | Mathematical/computational audit | Lean status |
|---|---|---|
| A qualifying 46-vertex counterexample exists | Certificate and exact invariants independently recomputed | Candidate source only; uncompiled |
| No qualifying counterexample has fewer than 46 vertices | Reduction and arithmetic reviewed; bounded relaxation reproduced | Graph-level proof not implemented |
| A counterexample exists at every order at least 46 | Construction reviewed; finite tests and algebra agree | Infinite graph construction not implemented |
| Every smallest counterexample has the stated profile | Arithmetic classification reviewed | Graph-level implication not implemented |

The research report itself explicitly distinguishes its informal proof from formal verification [1, pp. 1, 9]. That distinction remains necessary.

## 1. Scope and faithful interpretation

The target is the exact question on page 451 of Ghalavand’s paper: the largest order through which every connected simple graph with minimum degree two and maximum degree five satisfies the normalized Zagreb inequality [2]. The proposed answer is 45, with the first failure at 46 [1, Section 2].

The candidate definitions use actual Mathlib simple graphs on `Fin n`, not merely a list of numerical statistics. They require connectedness, all vertex degrees between two and five, and actual vertices attaining both endpoints. Edges are counted once by restricting to increasing vertex pairs. The violation is expressed with rational division in the original direction:

$$
\frac{M_2}{m}<\frac{M_1}{n}.
$$

The integer gap uses integer subtraction, not truncated natural subtraction. For graphs with the stated degree extrema, the order and size are positive. An intended lemma connects the explicitly computed neighbor count to Mathlib’s degree. None of these candidate definitions or lemmas has been elaborated by Lean here.


## 2. Mathematical re-audit

### Exact witness

A new verifier built an integer adjacency matrix directly from each supplied edge list. It rejected invalid or repeated edges, computed degrees from row sums, computed the second Zagreb index as half the degree-weighted adjacency sum, and checked connectivity using a bitset implementation of Warshall’s transitive closure. It imported none of the original verifier or constructor code.

For the canonical certificate it obtained

$$
(n,m,M_1,M_2)=(46,67,436,635),
\qquad mM_1-nM_2=2.
$$

Thus the normalized violation is exactly

$$
\frac{436}{46}-\frac{635}{67}=\frac{1}{1541}>0.
$$

This is an exact computational check, not a Lean certificate.

### Minimality argument

The reciprocal-incidence identity for the order, the edge sum for the first Zagreb index, and the quadratic gap expansion were re-derived. All 45 distinct edge-type coefficients were recomputed exactly. The coefficient for types $(2,5)$ and $(3,3)$ is $-1/30$; the other 44 are positive.

For candidate profiles, write $a=e_{25}$ and $b=e_{33}$. The source scales the report’s coefficients by 60:

$$
60D=2ab-A_{60}a-B_{60}b-C_{60},\qquad C_{60}\geq0.
$$

At order at most 46, $a+b\leq69$. If $A_{60},B_{60}\geq35$, then positivity of $D$ would require $2ab>35(a+b)$, while

$$
4ab\leq(a+b)^2\leq69(a+b),
$$

which is impossible. This is the same barrier as the report’s $7/12$ threshold, expressed with integer coefficients.

The five expensive defect types are therefore absent. Two cut conditions are needed to justify the remaining classification: there must be an edge from the degree-three vertices to their complement, and an edge between degree classes $\{2,5\}$ and $\{3,4\}$. Both follow informally from connectedness when $a,b>0$. Combined with the degree-four incidence equation, they leave precisely the report’s two defect patterns.

Pattern II gives the incompatible product bounds $XY\leq108900$ and $XY>126000$. Pattern I gives $a\equiv5\pmod{10}$ and $b\equiv1\pmod3$; the order and gap constraints leave only $a=35,b=31$. The case analysis was found internally consistent.

**Formal boundary:** the candidate profile theorem states its incidence and cut assumptions openly. Those assumptions have not been proved for every eligible Mathlib graph. The profile theorem must not be advertised as the completed graph-minimality theorem.

### Infinite construction

The report’s use of distinct subdivision vertices removes the parallel edges of its intermediate multigraph. Its hub cycle and matching give the stated hub degrees; the subdivided prism and bridge give the remaining degrees and connectivity. The reported order, size, and index formulas are consistent, and their gap identity was rechecked symbolically. The even and odd parameter choices cover all orders from 46 onward.

**Formal boundary:** numerical parameter existence does not prove graph realization. The infinite graph family and its general properties are not implemented in the candidate project.


## 3. Checks actually executed

| Check | Observed result |
|---|---|
| Original Python test suite | 18 test methods passed |
| Original certificate verifier | All seven certificates accepted |
| Original bounded edge-type relaxation | 3,003 defect patterns; 49,380 integral vectors |
| Connected degree-class support vectors | 36,641 |
| Positive-gap profiles in that relaxation | One, at order 46; none below 46 |
| Original NetworkX/SymPy cross-check | Passed |
| Fresh adjacency-matrix verifier | All seven certificates accepted |
| Exact pair coefficients | One negative, 44 positive |
| Fresh symbolic gap expansion | Identically zero difference |
| Actual generated Lean polynomial text | Symbolically consistent with the gap expansion |
| Regeneration of the two generated Lean modules | Byte-for-byte identical |
| Static scan of seven Lean files | No prohibited proof-placeholder or custom-axiom tokens found |
| Lean compilation or kernel checking | **Not performed** |

The bounded enumeration is a relaxation over numerical edge profiles, not an enumeration of all graphs. Its validity as an exclusion argument depends on the mathematical bounds and necessary conditions, as the supplied report correctly explains [1, Section 6].

\newpage

The fresh matrix results are:

| Certificate | Order | Edges | First index | Second index | Gap |
|---|---:|---:|---:|---:|---:|
| Canonical 46 | 46 | 67 | 436 | 635 | 2 |
| Family 46 | 46 | 67 | 436 | 635 | 2 |
| Family 47 | 47 | 69 | 438 | 643 | 1 |
| Family 48 | 48 | 70 | 454 | 662 | 4 |
| Family 49 | 49 | 72 | 456 | 670 | 2 |
| Family 100 | 100 | 148 | 922 | 1364 | 56 |
| Family 101 | 101 | 150 | 924 | 1372 | 28 |

### Execution evidence

The environment produced these actual errors:

```text
$ lean --version
lean: command not found
exit_status=127

$ lake --version
lake: command not found
exit_status=127

$ curl -I --max-time 15 https://github.com
curl: (6) Could not resolve host: github.com
exit_status=6
```

The package records ten subsequent command-launch attempts, including `lake build` and a `lake env lean` invocation for every Lean file. All failed to launch because the executables were absent. These are not successful compilation logs, and they are not diagnostics from a Lean compiler.

A static scan cannot detect all semantic problems or certify axiom dependencies. The supplied `Audit.lean` contains the intended `#print axioms` commands, but no output from those commands was obtained. The candidate proofs use ordinary `decide` rather than `native_decide`; that design choice is not a substitute for running the kernel [3].


## 4. Project inventory and remaining obligations

The project contains seven Lean files: a root import module, `Definitions`, `Arithmetic`, `Profiles`, `Witness`, `Targets`, and `Audit`. The witness includes a 45-edge spanning-tree reachability argument, actual degree and index computations, and an intended normalized-violation theorem. The arithmetic/profile modules encode the coefficient barrier and reduced cases. All are **uncompiled candidates**.

`Targets.lean` defines `Exists46Target`, `MinimalityTarget`, `AllOrdersTarget`, `ExtremalProfileTarget`, and their conjunction `FullTarget`. Defining a proposition, or checking the type of its name, does not prove it. No theorem of type `FullTarget` is supplied.

The remaining proof work is specific:

1. Compile and repair every candidate file; inspect the actual main-lemma axiom dependencies.
2. Prove edge-type exhaustion and the general double-counting identities for actual graphs.
3. Derive the incidence equations and both cut conditions from the graph hypotheses.
4. Relate actual order and gap to the profile expressions, then derive graph minimality and the extremal profile.
5. Define the infinite graph family and prove its simplicity, connectedness, exact degree extrema, order, edge counts, and Zagreb indices for all admissible parameters.
6. Combine the family with the parameter lemmas, prove the full target, and audit the resulting statement and proof dependencies.

These obligations are not filled by hidden assumptions or custom axioms. They are absent and explicitly documented. The source may also need ordinary compiler repairs that cannot be identified without execution.

### Versions and reproducibility

The selected target is Lean 4.19.0 and Mathlib commit

```text
c44e0c8ee63ca166450922a373c7409c5d26b00b
```

The commit and eight transitive dependency pins were read from a public project manifest that identifies this Mathlib revision with the `v4.19.0` tag [5]. The project’s `lake-manifest.json` was manually assembled from that data. It is **not a Lake-generated, tested lockfile**. A supplied script compares the fetched clones and Mathlib’s own manifest against these pins before compilation. This check has not run because the dependencies are absent.

After installing Lean through its official instructions [4], the intended local command is:

```bash
bash scripts/check_candidate.sh
```

It records actual local output, fetches the cache, checks dependency pins, builds the candidate library, and runs the candidate axiom audit. A successful run still covers only the implemented subresults. `LOCAL_FORMALIZATION_HANDOFF.md` specifies the missing mathematical work without weakening the target.

## 5. Publication assessment

The informal proof and numerical artifacts are suitable to send to a mathematician for independent scrutiny. This audit found no error, but it was conducted by the assistant within the same investigation, not by an independent referee.

The work is **not ready to be described as fully Lean-verified**, whether on arXiv, Substack, LinkedIn, or elsewhere. Formalization is incomplete, compiler acceptance is unknown, and bibliographic priority has not been established by this run. This finding does not itself refute the proposed mathematical theorem; it identifies the actual verification status.

The accurate present description is: *an unrefereed proposed solution, with reproducible computational checks and an uncompiled, partial Lean formalization draft.*

## References

[1] *The First Counterexample Has 46 Vertices*. Supplied Experiment 004 research report, 9 November 2026, 10 pages. Included unchanged as `input/research_report.pdf`; associated verification ZIP included as `input/original_verification.zip`.

[2] Ali Ghalavand. *On a Conjecture about Comparing the First and Second Zagreb Indices of Graphs*. MATCH 96 (2026), 441–452. Question I, p. 451. [Published paper](https://match.pmf.kg.ac.rs/electronic_versions/Match96/n2/match96n2_441-452.pdf).

[3] Lean Language Reference. *Validating Proofs*. Proof trust and statement validation. [Official documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

[4] Lean. *Manual Installation*. Toolchain installation and Mathlib project setup. [Official instructions](https://lean-lang.org/install/manual/).

[5] Public `tailored-LeanCat` project, `lake-manifest.json`. Source of the observed dependency pins; not the canonical Mathlib repository and not proof of successful resolution here. [Manifest source](https://github.com/banr1/tailored-LeanCat/blob/main/lake-manifest.json).

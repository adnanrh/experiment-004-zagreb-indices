# Manuscript preparation and validation report

**Status: complete author-review draft; no publication authorized or performed.**

## Deliverables and build

- Complete 10-page `amsart` manuscript, nine bibliography entries, generated bibliography, PDF, build instructions, and source ZIP.
- PDF built with pdfTeX 3.141592653-2.6-1.40.25, TeX Live 2023/Debian, and BibTeX 0.99d.
- Final local sequence: pdfLaTeX, BibTeX, pdfLaTeX, pdfLaTeX. All exit codes zero.
- Final LaTeX log: no warnings, overfull/underfull boxes, missing characters, unresolved citations, or unresolved cross-references. All PDF fonts embedded, with Unicode mappings; no bitmap Type 3 fonts.
- All ten rendered pages visually inspected, including equations, tables, author information, bibliography, and the full reproduction command block. No clipping, overlap, missing symbols, or isolated proof-ending marks remain.
- ZIP contains only `main.tex`, `references.bib`, and `main.bbl`. No figures or other assets are required.
- ZIP extracted into an empty temporary directory and independently rebuilt with pdfLaTeX/BibTeX/pdfLaTeX/pdfLaTeX, all exiting zero. Extracted final PDF text exactly matches the delivered PDF text; regenerated bibliography matches the bundled bibliography. Byte-identical PDF files are not claimed because build metadata can differ.
- Exact file hashes, command results, and temporary workspace path are in `build-results.json`. Final logs and ZIP-build transcripts are retained in this directory.

## Mathematical correspondence

The authoritative source is audited commit `68a494573fdbd2e629c620a263dafed5853ac26e`. The repository was clean at the start, at `1fd4a1b58f5e16dd24892a01f842cf480695abda`, which adds the supplied literature report. Its Lean source and dependency configuration match the audited mathematical revision.

The manuscript states exactly the universal inequality through order 45, actual order-46 existence, necessary order-46 profile, and actual graph existence for every integer order at least 46. Exact degree extrema, finiteness, simplicity, connectedness, inequality normalization and direction, and the distinction between profile uniqueness and isomorphism uniqueness are explicit.

The human-readable proof was checked against Definitions, Targets, Arithmetic, Profiles, GraphCounting, GraphTheorems, Witness, Family, Cores, and Full. The proof gives the counting identities, signed gap expansion, coefficient barrier, cut restrictions, five excluded edge types, the two remaining patterns, the contradiction for pattern II, and the full congruence/case argument for pattern I. It does not replace these arguments with a claim that Lean checked them.

`check_manuscript.py` additionally confirms with exact arithmetic:

- The Section 5 labeled witness edge set equals the actual `Witness.edgeList`, not merely its reported invariants.
- Its invariants are exactly `(n,m,M1,M2,D) = (46,67,436,635,2)` and its profile is `e25=35`, `e33=31`, `e23=1`.
- Both Section 6 labeled core edge sets equal the actual `Core5.edgeList` and `Core7.edgeList`.
- All scaled A/B/C penalty coefficients match `Profiles.lean` and the defining rational interaction formula.
- The three integrality-case rows are correct.
- The subdivided-rung construction has the stated counts and positive gap at 259 sampled orders, including 10000 and 10001. The samples supplement the symbolic proof, not establish the universal assertion.

No substantive mathematical discrepancy was found. The checked one-off witness subdivides a cycle edge; the completed infinite family subdivides a rung. The manuscript distinguishes them and proves their properties separately. Only the two fixed cores needed by FullTarget are asserted in the family lemma.

The six-defect bound is explained as an immediate consequence of the formal coefficient barrier and coefficient table; it is not represented as a separately named Lean theorem. Historical general-odd-core statements and graph-isomorphism classification are not added to the main claims.

## Historical sources and bibliography

The supplied `research/Zagreb_004_Independent_Novelty_Report.md` was read in full. Primary sources consulted during preparation included Ghalavand's journal PDF (Question I, printed page 451), Hansen--Vukicevic's publisher record, Andova--Cohen--Skrekovski's MATCH paper, the author-hosted Andova et al. prescribed-degrees paper, Vukicevic et al.'s MATCH paper, and Taubig's walk-count paper. The latter also supplies the older Lagarias--Mazo--Shepp--McKay reference. Bibliographic metadata agrees with the supplied novelty report.

The text acknowledges the earlier equivalent walk-count counterexamples, older degree-restricted connected constructions and infinite families, and the established edge-type method. It explicitly distinguishes the historical unrestricted 46-vertex example and does not describe 218 as a previous best bound. It claims no absolute bibliographic priority and does not claim to solve Question II.

Remaining literature limitation: the full Sun--Chen text was not obtained; DOI retrieval also failed during preparation. Its citation metadata comes from the supplied report, and no unexamined detailed result of that paper is used in the proof. The manuscript discloses this access gap and the incomplete bibliographic-database coverage. No citation metadata has been invented to fill a missing source.

## Verification and disclosure

The manuscript accurately reports the previously executed Lean build and axiom/dependency audit. Prior execution records were inspected; no new full Lean or Mathlib rebuild is claimed for this manuscript run. The isolated project audit reused dependency caches, and the final theorem's dependencies were limited to `propext`, `Classical.choice`, and `Quot.sound`.

The manuscript identifies the adversarial audit as AI-assisted and conducted by the same assistant involved in development. It does not claim independent human peer review, institutional certification, or proven novelty. Substantial generative-AI assistance, Adnan Husain's sole authorship and responsibility, Independent Researcher affiliation, and the supplied ORCID are present. The intended submission category is math.CO; no arXiv identifier has been created.

## Scope preservation and approval

Only new files under `manuscript/arxiv/` were created. Existing tracked files are unchanged, including all Lean sources, pins, manifests, verification scripts, certificates, and research artifacts. Historical stale headers and checksum files were preserved.

Standard TeX/Poppler/font packages were installed in the WSL environment to enable compilation and visual inspection; Lean dependencies were not changed. `git diff --check` and shell syntax validation passed. The work remains uncommitted and unpushed. No tag, release, pull request, arXiv submission, or social publication was created.

**Await explicit author review and approval. External independent mathematical review remains outstanding.**

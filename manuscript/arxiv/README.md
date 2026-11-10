# Experiment 004 arXiv manuscript

Author-review draft. Intended category: **math.CO**. No arXiv submission or publication has been performed.

## Files

- `main.tex`: complete manuscript, using the standard `amsart` class.
- `references.bib`: nine bibliography entries.
- `main.bbl`: generated bibliography, included for arXiv compilation.
- `main.pdf`: compiled manuscript.
- `arxiv-source.zip`: submission sources only (`main.tex`, `references.bib`, `main.bbl`); no PDF, logs, caches, or validation materials.
- `build.sh`: local PDF, bibliography, and ZIP build.
- `validation/`: manuscript consistency checks and build/validation report.
- `build/`: ignored intermediate LaTeX files and rendered page images.

No figures or external assets are required. The constructions are specified by explicit vertices and edges in the text.

## Build locally

Requirements: a standard TeX Live installation with `amsart`, `amsmath`, `amssymb`, `amsthm`, `booktabs`, `array`, `geometry`, `hyperref`, T1 encoding, Latin Modern fonts, and BibTeX; Bash and Python 3.10+ for the build wrapper. No shell escape is used.

On Ubuntu, the packages used for this build were `texlive-latex-recommended`, `texlive-fonts-recommended`, `lmodern`, and `poppler-utils` (the last for PDF inspection).

From this directory:

```bash
bash build.sh
python3 validation/check_manuscript.py
python3 validation/check_submission.py
```

The mathematical check requires this manuscript directory to remain inside the Experiment 004 checkout. It compares the human-readable witness and core labels and all penalty coefficients to the existing Lean source; its finite graph checks supplement the proof, not replace it. It does not modify source or certificates.

The underlying typesetting sequence is:

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

To test the ZIP, extract its three files into an empty directory and run this sequence there. The bundled `main.bbl` also permits compilation without a new BibTeX run. Use `main.tex` as the submission entry point. The ZIP intentionally excludes the local build wrapper and this README because neither is needed by arXiv.

## Mathematical source and review limits

The authoritative mathematical revision is `68a494573fdbd2e629c620a263dafed5853ac26e` (Lean 4.19.0; Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`). Manuscript preparation began at repository HEAD `1fd4a1b58f5e16dd24892a01f842cf480695abda`; the Lean files and dependency configuration at that HEAD are unchanged from the audited mathematical revision.

The manuscript follows the actual checked `Witness.lean` construction in Section 5 and the two fixed cores plus subdivided-rung prism from `Cores.lean` and `Family.lean` in Section 6. It does not substitute the historical Python family for the formally checked family or assert a formal arbitrary-odd-core theorem.

Historical context was checked against `research/Zagreb_004_Independent_Novelty_Report.md` and accessible cited primary sources. The Sun--Chen full text remains an acknowledged access limitation; its bibliographic metadata is supplied by the novelty report. No assertion of absolute priority or independent human peer review is made. Substantial AI assistance and sole human-author responsibility are disclosed in the manuscript.

The manuscript reports the prior executed Lean audit; manuscript preparation is not a new clean rebuild of Lean or Mathlib. The additional adversarial audit was AI-assisted and conducted by the same assistant involved in development. External independent mathematical review remains outstanding.

Review `validation/REPORT.md` before author approval. Nothing in this directory authorizes a commit, push, arXiv submission, or other publication.

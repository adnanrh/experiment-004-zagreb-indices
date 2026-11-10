#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass1.txt 2>&1
BIBINPUTS=.: bibtex build/main > build/bibtex.txt 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass2.txt 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass3.txt 2>&1
cp build/main.pdf main.pdf
cp build/main.bbl main.bbl
python3 - <<'PY'
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
with ZipFile('arxiv-source.zip', 'w', compression=ZIP_DEFLATED) as z:
    for name in ('main.tex', 'references.bib', 'main.bbl'):
        z.write(name, name)
print('Built main.pdf and arxiv-source.zip')
PY

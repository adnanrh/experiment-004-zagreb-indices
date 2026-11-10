#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p local-logs
exec > >(tee local-logs/candidate-check.txt) 2>&1
set -x
command -v lake
lake env lean --version
python3 scripts/audit_sources.py
# Cache download is an installation step and needs network access on a fresh machine.
lake exe cache get
python3 scripts/check_dependency_pins.py
lake build
lake env lean Audit.lean
set +x
printf '\nCOMPLETED FORMALIZATION CHECK FINISHED.\n'
printf 'Inspect Audit.lean output: only standard Lean axioms should occur.\n'
printf 'The project proves MinimalityTarget, AllOrdersTarget, and the complete FullTarget.\n'
printf 'Audit.lean checks Zagreb004.fullTarget and prints its axiom dependencies.\n'

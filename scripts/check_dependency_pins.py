#!/usr/bin/env python3
"""Compare actual clones and Mathlib's own lockfile to the supplied pins.
Run AFTER Lake has fetched dependencies. Fail closed on absent or mismatched data.
"""
import json
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    lock=json.loads((ROOT/'lake-manifest.json').read_text())
    got={p['name']:p for p in lock['packages']}
    for name,p in got.items():
        folder=ROOT/lock['packagesDir']/name
        if not folder.is_dir(): raise SystemExit(f'NOT VERIFIED: dependency absent: {name}')
        actual=subprocess.check_output(['git','-C',str(folder),'rev-parse','HEAD'],text=True).strip()
        if actual!=p['rev']: raise SystemExit(f'PIN MISMATCH: {name}: {actual} != {p["rev"]}')
    tool=(ROOT/lock['packagesDir']/'mathlib'/'lean-toolchain').read_text().strip()
    if tool!=(ROOT/'lean-toolchain').read_text().strip():
        raise SystemExit('TOOLCHAIN MISMATCH with Mathlib')
    upstream=json.loads((ROOT/lock['packagesDir']/'mathlib'/'lake-manifest.json').read_text())
    for p in upstream['packages']:
        if p['name'] not in got or got[p['name']]['rev']!=p['rev']:
            raise SystemExit(f'UPSTREAM LOCKFILE MISMATCH: {p["name"]}')
    print('Dependency commit IDs and upstream Mathlib pins agree. This is not a proof audit.')

if __name__=='__main__': main()

#!/usr/bin/env python3
"""Record real command attempts. Missing executables are NOT Lean failures or successes."""
from pathlib import Path
import json
import subprocess
ROOT=Path(__file__).resolve().parents[1]

def main():
    sources=['Zagreb004/Definitions.lean','Zagreb004/Arithmetic.lean',
             'Zagreb004/Profiles.lean','Zagreb004/Witness.lean',
             'Zagreb004/Targets.lean','Zagreb004.lean','Audit.lean']
    commands=[['lean','--version'],['lake','--version'],['lake','build']]
    commands += [['lake','env','lean',s] for s in sources]
    records=[]
    for command in commands:
        try:
            p=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,timeout=120,check=False)
            rec={'command':command,'launched':True,'exit_code':p.returncode,'output':p.stdout}
        except FileNotFoundError as ex:
            rec={'command':command,'launched':False,'exit_code':127,'output':str(ex)}
        except subprocess.TimeoutExpired as ex:
            rec={'command':command,'launched':True,'exit_code':124,'output':str(ex)}
        records.append(rec)
    dest=ROOT/'logs/compile_attempts.json'
    dest.write_text(json.dumps({'notice':'These are actual attempts, not successful compilation logs.',
                               'records':records},indent=2)+'\n')
    with (ROOT/'logs/compile_attempts.txt').open('w') as f:
        for r in records:
            f.write('$ '+' '.join(r['command'])+'\n'+r['output']+'\n')
            f.write(f'launched={r["launched"]}; exit_status={r["exit_code"]}\n\n')
    print(f'Recorded {len(records)} command attempts; {sum(r["launched"] for r in records)} launched.')
    if not all(r['launched'] and r['exit_code']==0 for r in records): raise SystemExit(1)

if __name__=='__main__': main()

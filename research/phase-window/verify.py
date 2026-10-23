"""Build the standalone package, audit exported axioms, and reproduce exact tests."""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def run(command, logfile):
    result = subprocess.run(command, cwd=ROOT, text=True, encoding='utf-8',
                            errors='replace', stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT/logfile).write_text(result.stdout, encoding='utf-8')
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(f'Failed: {command[0]} (exit {result.returncode})')
    return result.stdout

def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    lake = shutil.which('lake')
    if not lake and os.name == 'nt':
        candidate=Path.home()/'.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake.exe'
        if candidate.exists():
            lake=str(candidate)
    if not lake:
        raise SystemExit('Install elan/Lean 4.34.0, then run this script again.')
    for source in list((ROOT/'PhaseWindow').glob('*.lean'))+[ROOT/'PhaseWindow.lean']:
        if re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',source.read_text(encoding='utf-8-sig')):
            raise SystemExit(f'Forbidden proof declaration or tactic in {source.name}')
    run([lake,'build'],'build.log')
    audit=run([lake,'env','lean','PhaseWindow.lean'],'axioms.log')
    allowed={'propext','Classical.choice','Quot.sound'}
    reports=re.findall(r'depends on axioms: \[([^\]]*)\]',audit)
    if len(reports)!=15:
        raise SystemExit(f'Expected 15 axiom reports, found {len(reports)}')
    for report in reports:
        if set(report.split(', '))-allowed:
            raise SystemExit('Unexpected axiom in audit')
    result=run([sys.executable,'probe_windows.py'],'experiment-results.json')
    json.loads(result)
    result=run([sys.executable,'probe_relation.py'],'relation-results.json')
    json.loads(result)
    result=run([sys.executable,'probe_triple.py'],'triple-results.json')
    json.loads(result)
    result=run([sys.executable,'probe_descent.py'],'descent-results.json')
    json.loads(result)
    print('PASS: build, 15 exported axiom audits, and exact rational experiments.')

if __name__=='__main__':
    main()

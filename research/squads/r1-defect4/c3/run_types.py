#!/usr/bin/env python3
"""Run gen_type.py + kissat for every cycle type in a list, sequentially (THREADS=1).
usage: run_types.py k types_file outdir [--timeout 900] [--nolex] [--verify]
types_file: one comma-separated cycle type per line (lines starting with '#' ignored).
Writes outdir/results.tsv (type, result, seconds) and prints a summary line.
Instance is UNSAT (no (k,3,-4)-graph) iff every type is UNSAT."""
import sys, os, subprocess, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_type import build
from pysat.formula import CNF

ap = argparse.ArgumentParser()
ap.add_argument('k', type=int)
ap.add_argument('types_file')
ap.add_argument('outdir')
ap.add_argument('--timeout', type=int, default=900)
ap.add_argument('--nolex', action='store_true')
ap.add_argument('--verify', action='store_true')
a = ap.parse_args()
KISSAT = '/tmp/claude-0/-home-user-degree-diameter/4905f117-080d-5578-b5d8-53a7377d03a3/scratchpad/kissat/build/kissat'
HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(a.outdir, exist_ok=True)
types = [l.strip() for l in open(a.types_file) if l.strip() and not l.startswith('#')]
tsv = open(os.path.join(a.outdir, 'results.tsv'), 'a')
counts = {'UNSAT': 0, 'SAT': 0, 'TIMEOUT': 0}
total = 0.0
for t in types:
    parts = [int(x) for x in t.split(',')]
    name = t.replace(',', '_')
    cnf_path = os.path.join(a.outdir, f't_{name}.cnf')
    out_path = os.path.join(a.outdir, f't_{name}.out')
    cnf, _, _ = build(a.k, parts, lex=not a.nolex)
    cnf.to_file(cnf_path)
    s = time.time()
    try:
        p = subprocess.run(['timeout', str(a.timeout), 'nice', '-n', '10', KISSAT, '-q', cnf_path],
                           capture_output=True, text=True)
        rc = p.returncode
        with open(out_path, 'w') as f:
            f.write(p.stdout)
    except Exception as e:
        rc = -1
    dt = time.time() - s
    total += dt
    res = {10: 'SAT', 20: 'UNSAT'}.get(rc, 'TIMEOUT')
    counts[res] += 1
    line = f'{t}\t{res}\t{dt:.2f}'
    if res == 'SAT' and a.verify:
        v = subprocess.run([sys.executable, os.path.join(HERE, 'verify_sat.py'), str(a.k), out_path],
                           capture_output=True, text=True)
        line += '\t' + (v.stdout.strip() or v.stderr.strip().splitlines()[-1])
    tsv.write(line + '\n'); tsv.flush()
    print(line, flush=True)
    if res == 'UNSAT' and os.path.exists(out_path):
        os.remove(out_path)
    os.remove(cnf_path) if res == 'UNSAT' else None
print(f'SUMMARY k={a.k} types={len(types)} UNSAT={counts["UNSAT"]} SAT={counts["SAT"]} '
      f'TIMEOUT={counts["TIMEOUT"]} total_seconds={total:.1f} nolex={a.nolex}', flush=True)

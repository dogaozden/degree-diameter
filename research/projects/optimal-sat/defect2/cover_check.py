#!/usr/bin/env python3
"""Check that the cubes of cube_list.py cover the whole search space: F' = F + {not c : c surviving}; DRAT proof =
the negations of all tree nodes in post-order (refuted nodes are RUP by unit propagation, inner nodes by resolution of
their two children), ending with the empty clause. Then: every surviving cube UNSAT (run_cube.sh) + this check
VERIFIED  =>  F UNSAT.  usage: cover_check.py cubes.json workdir   (env DRATTRIM)"""
import sys, os, json, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enc_quot import build
d = json.load(open(sys.argv[1])); wd = sys.argv[2]; os.makedirs(wd, exist_ok=True)
o = d['opts']
cnf, pool, a = build(d['k'], sym='--sym' in o, nf2='--nf2' in o, ntt='--ntt' in o, alltr='--alltr' in o, signs='--signs' in o)
for c in d['surviving']: cnf.append([-l for l in c])
fp = os.path.join(wd, 'cover.cnf'); pp = os.path.join(wd, 'cover.drat'); cnf.to_file(fp)
leaves = set(tuple(c) for c in d['surviving']) | set(tuple(c) for c in d['refuted'])
cv = d['cube_vars']
lines = []
survset = set(tuple(c) for c in d['surviving'])
def post2(pre):
    t = tuple(pre)
    if t in survset: return
    if t in leaves: lines.append([-l for l in pre]); return
    v = cv[len(pre)]
    post2(pre + [-v]); post2(pre + [v]); lines.append([-l for l in pre])
post2([])
with open(pp, 'w') as f:
    for cl in lines: f.write(' '.join(map(str, cl)) + ' 0\n')
r = subprocess.run([os.environ.get('DRATTRIM', 'drat-trim'), fp, pp, '-t', '200000'], capture_output=True, text=True)
ok = 's VERIFIED' in r.stdout.replace('\r', '')
print(f'cover check: {len(d["surviving"])} surviving cubes, {len(d["refuted"])} refuted nodes, '
      f'{len(lines)} lemmas: {"VERIFIED" if ok else "NOT VERIFIED"}')
os.remove(fp); os.remove(pp)

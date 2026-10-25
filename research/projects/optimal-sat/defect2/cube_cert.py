#!/usr/bin/env python3
"""Certified cube-and-conquer for the quotient instance.
Cubes: all 0/1 assignments to the arcs (x, z) for x in the first `rows` vertices of O and z in I. Cubes refuted by
unit propagation are written to a list (they need no proof beyond propagation; drat-trim checks them too if --all).
Each surviving cube: CNF + unit clauses -> kissat with binary DRAT -> drat-trim -> log line; proof deleted.
The cubes cover all assignments of those variables, so UNSAT of every cube = UNSAT of the instance.
usage: cube_cert.py k "encoder options" outdir rows jobs"""
import sys, os, itertools, subprocess, hashlib, json, time
from concurrent.futures import ThreadPoolExecutor
from pysat.solvers import Cadical153
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enc_quot import build

k = int(sys.argv[1]); opts = sys.argv[2].split(); out = sys.argv[3]; rows = int(sys.argv[4]); jobs = int(sys.argv[5])
KISSAT = os.environ.get('KISSAT', 'kissat'); DRATTRIM = os.environ.get('DRATTRIM', 'drat-trim')
os.makedirs(out, exist_ok=True)
g = k - 2
cnf, pool, a = build(k, signs='--signs' in opts, sym='--sym' in opts, nf2='--nf2' in opts,
                     ntt='--ntt' in opts, alltr='--alltr' in opts)
base = os.path.join(out, 'base.cnf'); cnf.to_file(base)
sha = hashlib.sha256(open(base, 'rb').read()).hexdigest()
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
cv = [a[x, z] for x in O[:rows] for z in I]
s = Cadical153(bootstrap_with=cnf.clauses)
surv = []; dead = 0
for bits in itertools.product((0, 1), repeat=len(cv)):
    cube = [v if b else -v for v, b in zip(cv, bits)]
    ok, _ = s.propagate(assumptions=cube)
    if ok: surv.append(cube)
    else: dead += 1
log = open(os.path.join(out, 'cubes.log'), 'a')
print(f'k={k} opts={opts} base sha256 {sha} vars={cnf.nv} clauses={len(cnf.clauses)} cube vars={len(cv)} '
      f'refuted by propagation={dead} surviving={len(surv)}', file=log, flush=True)
json.dump({'cube_vars': cv, 'surviving': surv}, open(os.path.join(out, 'cubes.json'), 'w'))
nclauses = len(cnf.clauses)
def run(i):
    cube = surv[i]
    f = os.path.join(out, f'c{i}.cnf'); p = os.path.join(out, f'c{i}.drat')
    with open(base) as fin, open(f, 'w') as fo:
        hdr = fin.readline().split(); fo.write(f'p cnf {hdr[2]} {nclauses + len(cube)}\n')
        for line in fin: fo.write(line)
        for l in cube: fo.write(f'{l} 0\n')
    t0 = time.time()
    r = subprocess.run([KISSAT, '-q', f, p], capture_output=True, text=True)
    t1 = time.time()
    res = 'SAT' if r.returncode == 10 else ('UNSAT' if r.returncode == 20 else f'rc{r.returncode}')
    chk = ''
    if res == 'UNSAT':
        c = subprocess.run([DRATTRIM, f, p, '-t', '200000'], capture_output=True, text=True)
        chk = 'VERIFIED' if 's VERIFIED' in c.stdout.replace('\r', '') else 'NOT-VERIFIED'
        os.remove(p)
    os.remove(f)
    line = f'cube {i} {res} solve {t1 - t0:.1f}s check {time.time() - t1:.1f}s {chk}'
    print(line, file=log, flush=True)
    return res, chk
with ThreadPoolExecutor(jobs) as ex:
    res = list(ex.map(run, range(len(surv))))
# Cover check: F' = F + {not c : c surviving}; proof = negated prefixes bottom-up over the full cube tree; the
# refuted leaves are RUP by unit propagation, internal nodes by resolution, the root is the empty clause.
fp = os.path.join(out, 'cover.cnf'); pp = os.path.join(out, 'cover.drat')
survset = set(tuple(c) for c in surv)
with open(base) as fin, open(fp, 'w') as fo:
    hdr = fin.readline().split(); fo.write(f'p cnf {hdr[2]} {nclauses + len(surv)}\n')
    for line in fin: fo.write(line)
    for c in surv: fo.write(' '.join(str(-l) for l in c) + ' 0\n')
with open(pp, 'w') as fo:
    for d in range(len(cv), -1, -1):
        for bits in itertools.product((0, 1), repeat=d):
            pre = [v if b else -v for v, b in zip(cv, bits)]
            if d == len(cv) and tuple(pre) in survset: continue
            fo.write(' '.join(str(-l) for l in pre) + ' 0\n')
c = subprocess.run([DRATTRIM, fp, pp, '-t', '200000'], capture_output=True, text=True)
cover = 'VERIFIED' if 's VERIFIED' in c.stdout.replace('\r', '') else 'NOT-VERIFIED'
print(f'cover check (cubes are exhaustive, refuted cubes by unit propagation): {cover}', file=log, flush=True)
os.remove(fp); os.remove(pp)
allok = all(r == ('UNSAT', 'VERIFIED') for r in res) and cover == 'VERIFIED'
print(f'DONE all {len(surv)} surviving cubes UNSAT and VERIFIED: {allok}; SAT cubes: {sum(r[0]=="SAT" for r in res)}', file=log, flush=True)

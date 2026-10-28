"""spreadsat.py: is there a (near-)line spread of Q(6,q) (a partition of its points into totally singular lines) invariant
under a cyclic collineation group <h> of H(q)? Exact cover of the point orbits by admissible t.s.-line orbits, solved
with CaDiCaL (pysat): every full-size point orbit exactly once, smaller orbits at most once. Inputs: the orbit quotient files of tsorbq.c (PREFIX.reps, PREFIX.osz; built with MINSIZE 1)
and the point orbits (PORB). With TARGET, solves the packing version instead: at most one per point orbit and at least TARGET
full-size line orbits.
Usage: python3 spreadsat.py PREFIX PORB Q SECONDS [TARGET]"""
import sys
import numpy as np
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

pre, porbf, q, secs = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4])
target = int(sys.argv[5]) if len(sys.argv) > 5 else None
reps = np.fromfile(pre + '.reps', dtype=np.int32).reshape(-1, q + 1).astype(np.int64)
osz = np.fromfile(pre + '.osz', dtype=np.int32).astype(np.int64)
porb = np.fromfile(porbf, dtype=np.int32).astype(np.int64)
psz = np.bincount(porb)
n = len(reps); no = len(psz)
cover = [[] for _ in range(no)]                    # options covering each point orbit
bad = 0
for v in range(n):
    o, cnt = np.unique(porb[reps[v]], return_counts=True)
    c = osz[v] * cnt / psz[o]
    if not np.all(c == 1):
        bad += 1; continue                          # covers some points of an orbit but not all: never in an exact cover
    for x in o:
        cover[x].append(v + 1)
print(f'{n} admissible line orbits, {bad} unusable for an exact cover; {no} point orbits; '
      f'options per point orbit: min {min(map(len, cover))} max {max(map(len, cover))}', flush=True)
pool = IDPool(start_from=n + 1)
S = Cadical153()
for x in range(no):
    if not cover[x]:
        print(f'point orbit {x} (size {psz[x]}) has no option', flush=True); continue
    if target is None and psz[x] == psz.max():
        enc = CardEnc.equals(lits=cover[x], bound=1, vpool=pool, encoding=EncType.seqcounter)
    elif len(cover[x]) > 1:
        enc = CardEnc.atmost(lits=cover[x], bound=1, vpool=pool, encoding=EncType.seqcounter)
    else:
        continue
    for cl in enc.clauses:
        S.add_clause([int(l) for l in cl])
if target is not None:                             # TARGET = number of full-size line orbits
    full = [v + 1 for v in range(n) if osz[v] == osz.max()]
    enc = CardEnc.atleast(lits=full, bound=target, vpool=pool, encoding=EncType.cardnetwrk)
    for cl in enc.clauses:
        S.add_clause([int(l) for l in cl])
print(f'{S.nof_vars()} variables, {S.nof_clauses()} clauses; solving (run under timeout {secs:.0f})', flush=True)
res = S.solve()                                     # CaDiCaL in pysat cannot be interrupted: use an outer timeout
print('result:', 'SAT' if res else 'UNSAT', flush=True)
if res:
    m = S.get_model(); sol = [v for v in range(n) if m[v] > 0]
    print(f'{len(sol)} orbits, {int(osz[sol].sum())} lines')
    np.savetxt(pre + '_spread.txt', np.array(sol), fmt='%d')

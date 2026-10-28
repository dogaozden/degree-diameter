"""ovoidsat.py: the point version of spreadsat.py: a set of points of H(q), invariant under <h>, meeting every
full-size line orbit's lines exactly once and the other lines at most once (a near distance-2 ovoid), by SAT.
Inputs: point orbits (PORB) and hexagon-line orbits (LORB, from lineorbquot.py) of the same group.
With TARGET: at most once everywhere and at least TARGET full-size point orbits (packing version).
Usage: python3 ovoidsat.py HEXBIN PORB LORB [TARGET]"""
import sys
sys.path.insert(0, '..')
import numpy as np
from hexlib import Hex
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

H = Hex(sys.argv[1])
porb = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64)
lorb = np.fromfile(sys.argv[3], dtype=np.int32).astype(np.int64)
psz, lsz = np.bincount(porb), np.bincount(lorb)
npo, nlo = len(psz), len(lsz)
rep = np.full(npo, -1); 
for p in range(H.N - 1, -1, -1):
    rep[porb[p]] = p
cover = [[] for _ in range(nlo)]; opts = []
for o in range(npo):
    lo, cnt = np.unique(lorb[H.PL[rep[o]]], return_counts=True)
    c = psz[o] * cnt / lsz[lo]
    if not np.all(c == 1):
        continue
    opts.append(o)
    for x in lo:
        cover[x].append(len(opts))
print(f'{npo} point orbits, {len(opts)} usable; {nlo} line orbits; options per line orbit min {min(map(len, cover))}', flush=True)
pool = IDPool(start_from=len(opts) + 1); S = Cadical153()
for x in range(nlo):
    if not cover[x]:
        print(f'line orbit {x} (size {lsz[x]}) has no option', flush=True); continue
    if len(sys.argv) < 5 and lsz[x] == lsz.max():
        enc = CardEnc.equals(lits=cover[x], bound=1, vpool=pool, encoding=EncType.seqcounter)
    elif len(cover[x]) > 1:
        enc = CardEnc.atmost(lits=cover[x], bound=1, vpool=pool, encoding=EncType.seqcounter)
    else:
        continue
    for cl in enc.clauses:
        S.add_clause([int(l) for l in cl])
if len(sys.argv) > 4:
    full = [i + 1 for i, o in enumerate(opts) if psz[o] == psz.max()]     # TARGET = number of full-size orbits
    enc = CardEnc.atleast(lits=full, bound=int(sys.argv[4]), vpool=pool, encoding=EncType.totalizer)
    for cl in enc.clauses:
        S.add_clause([int(l) for l in cl])
print(f'{S.nof_vars()} variables, {S.nof_clauses()} clauses', flush=True)
res = S.solve()
print('result:', 'SAT' if res else 'UNSAT', flush=True)
if res:
    m = S.get_model(); sol = [opts[i] for i in range(len(opts)) if m[i] > 0]
    pts = np.where(np.isin(porb, sol))[0]
    print(f'{len(sol)} point orbits, {len(pts)} points'); np.savetxt('ovoidsat_points.txt', pts, fmt='%d')

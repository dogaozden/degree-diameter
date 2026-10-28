"""Card c5: fix a freed set R of W(5) points, then SAT-search a bijection M: points -> lines satisfying (E1)-(E3).
usage: python3 fixedR_sat.py MODE K SEED TIMEOUT_S
  MODE = ovoid  : R = random greedy partial ovoid (pairwise non-collinear) of size K (or as large as found)
         deg4   : R = random greedy set with at most 4 collinear neighbours inside R (weaker than partial ovoid)
Writes best.json-style output to stdout as JSON {"R":..., "M":...} when SAT."""
import sys, json, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from gqlib import W
from repair import exact_conditions, brute_bad

mode, K, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
G = W(5)
n = G.np; assert G.nl == n == 156
rng = random.Random(seed)

def pick_R(K):
    order = list(range(n)); rng.shuffle(order)
    R = []
    for p in order:
        if len(R) >= K: break
        if mode == 'ovoid':
            if all(not G.col[p, x] for x in R): R.append(p)
        else:  # deg4: each point of R has <=4 collinear neighbours in R
            if sum(G.col[p, x] for x in R) <= 4 and all(sum(G.col[x, y] for y in R) + G.col[x, p] <= 4 for x in R):
                R.append(p)
    return R

R = pick_R(K)
print('R size', len(R), file=sys.stderr)
Rset = set(R)
pool = IDPool()
m = lambda p, l: pool.id(('m', p, l))
cl = []
for p in range(n):
    cl.append([m(p, l) for l in range(n)])
    cl += CardEnc.atmost([m(p, l) for l in range(n)], 1, vpool=pool, encoding=EncType.seqcounter).clauses
for l in range(n):
    cl.append([m(p, l) for p in range(n)])
    cl += CardEnc.atmost([m(p, l) for p in range(n)], 1, vpool=pool, encoding=EncType.seqcounter).clauses
# E1: s_l = line l is an image of a freed point; no point has all six lines in M(R)
s = lambda l: pool.id(('s', l))
for x in R:
    for l in range(n):
        cl.append([-m(x, l), s(l)])
for p in range(n):
    cl.append([-s(l) for l in G.plines[p]])
# E2: for x in R and every point q: some a in Gamma2(x) minus R has M(a) through q
for x in R:
    a_set = [a for a in np.nonzero(G.col[x])[0] if a not in Rset]
    for q in range(n):
        cl.append([m(a, l) for a in a_set for l in G.plines[q]])
# E3: t(x,l) = M(x) concurrent with l ; z(x,a) = M(a) concurrent with M(x), a not in R
t = lambda x, l: pool.id(('t', x, l))
z = lambda x, a: pool.id(('z', x, a))
for x in R:
    for l in range(n):
        cl.append([-t(x, l)] + [m(x, L) for L in np.nonzero(G.con[l])[0]])
    for a in range(n):
        if a in Rset: continue
        for l in range(n):
            cl.append([-z(x, a), -m(a, l), t(x, l)])
    for u in range(n):   # every line u contains a point a not in R with z(x,a)
        cl.append([z(x, a) for a in G.lines[u] if a not in Rset])
# symmetry: fix nothing else (keep search general)
t0 = time.time()
with Solver(name='cadical153', bootstrap_with=cl) as S:
    ok = S.solve()
    print('SAT' if ok else 'UNSAT', 'vars', pool.top, 'clauses', len(cl), 'time %.1f' % (time.time() - t0), file=sys.stderr)
    if not ok:
        print(json.dumps({'R': R, 'sat': False}))
        sys.exit(0)
    model = set(v for v in S.get_model() if v > 0)
M = [None] * n
for p in range(n):
    for l in range(n):
        if m(p, l) in model: M[p] = l
good, fails = exact_conditions(G, 'H', 'H', M, R)
bad = brute_bad(G, 'H', 'H', M, R)
print('exact_conditions', good, 'brute_bad', bad, 'R', len(R), file=sys.stderr)
print(json.dumps({'R': [int(x) for x in R], 'M': [int(x) for x in M], 'ok': bool(good), 'brute_bad': int(bad)}))

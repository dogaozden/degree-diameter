"""Mixed centres by regulus switching, then whiskers on both sides by ILP; writes the m = 2 doubled graph.

Start: the Hermitian spread S of H(q) (all S-lines are centres, level 1; no level 2). Switch r disjoint S-reguli
(blocks of the unital): their q+1 lines leave A0 and the q+1 points whose shadows partition them become point centres
(level 1) with their q+1 lines in A0. Then choose whiskers (lines through points of kept S-lines) and dual whiskers
(points on lines of point centres) so that every vertex outside A0 sees at most one (ideally exactly one) A0 vertex.
Trees: centre, its neighbours, leaves; Theorem 1 + Lemma 2 give diameter 6.

python3 switch_ilp.py q r SECONDS [seed] [exact]
"""
import json
import random
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix, lil_matrix
from scipy.sparse.csgraph import shortest_path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
q, r, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4].isdigit() else 1
exact = 'exact' in sys.argv
rng = random.Random(seed)
t0 = time.time()
lines = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())['lines']
R = json.loads((HERE / f'reguli_q{q}.json').read_text())
S, reg = R['S'], R['reguli']
N = len(lines)
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
rows = [p for k, L in enumerate(lines) for p in L]
cols = [N + k for k, L in enumerate(lines) for p in L]
G = csr_matrix((np.ones(2 * len(rows)), (rows + cols, cols + rows)), shape=(2 * N, 2 * N))

# choose r disjoint blocks whose centres are pairwise opposite (greedy, random order)
dcache = {}


def dist(P):
    if P not in dcache:
        dcache[P] = shortest_path(G, unweighted=True, indices=P)
    return dcache[P]


best = []
for attempt in range(20):
    order = list(range(len(reg)))
    rng.shuffle(order)
    used, chosen = set(), []
    for b in order:
        Ls, Ps, _ = reg[b]
        if used & set(Ls):
            continue
        cen = [P for bb in chosen for P in reg[bb][1]]
        if all(dist(P)[P2] == 6 for P in Ps for P2 in cen):
            chosen.append(b)
            used |= set(Ls)
            if len(chosen) == r:
                break
    if len(chosen) > len(best):
        best = chosen
    if len(best) == r:
        break
print('blocks chosen', len(best), 'of', r, f'({time.time()-t0:.0f}s)', flush=True)
removed = {k for b in best for k in reg[b][0]}
S1 = [k for k in S if k not in removed]
Pc = [P for b in best for P in reg[b][1]]
A0P = {p for k in S1 for p in lines[k]} | set(Pc)
A0L = set(S1) | {k for P in Pc for k in through[P]}
wcand = sorted({k for k in S1 for p in lines[k] for k in through[p]} - A0L)
ucand = sorted({p for P in Pc for k in through[P] for p in lines[k]} - A0P)
print('centres: lines', len(S1), 'points', len(Pc), '| fixed A0 points', len(A0P), 'lines', len(A0L),
      '| candidates whiskers', len(wcand), 'dual', len(ucand), flush=True)
wi = {k: i for i, k in enumerate(wcand)}
ui = {p: len(wcand) + i for i, p in enumerate(ucand)}
nv = len(wcand) + len(ucand)
M = lil_matrix((2 * N, nv))
lo, hi = [], []
row = 0
for y in range(N):  # points outside fixed A0: whiskers through y + fixed A0 lines through y <= 1 (== 1 exact)
    if y in A0P:
        continue
    F = sum(k in A0L for k in through[y])
    for k in through[y]:
        if k in wi:
            M[row, wi[k]] = 1
    lo.append(1 - F if exact else -np.inf)
    hi.append(1 - F)
    row += 1
for k in range(N):  # lines outside fixed A0
    if k in A0L:
        continue
    F = sum(p in A0P for p in lines[k])
    for p in lines[k]:
        if p in ui:
            M[row, ui[p]] = 1
    lo.append(1 - F if exact else -np.inf)
    hi.append(1 - F)
    row += 1
M = M[:row].tocsr()
bad = [i for i in range(row) if hi[i] < 0]
print('rows', row, 'infeasible rows (F >= 2)', len(bad), flush=True)
res = milp(-np.ones(nv), constraints=[LinearConstraint(M, lo, hi)], integrality=np.ones(nv), bounds=Bounds(0, 1),
           options={'time_limit': secs})
print(res.message, f'({time.time()-t0:.0f}s)', flush=True)
if res.x is None:
    raise SystemExit
x = np.round(res.x).astype(int)
W = [k for k in wcand if x[wi[k]]]
U = [p for p in ucand if x[ui[p]]]
a_P, a_L = len(A0P) + len(U), len(A0L) + len(W)
c = len(S1) + len(Pc)
print('whiskers', len(W), 'dual', len(U), 'bound', getattr(res, 'mip_dual_bound', None))
print('A0 points', a_P, 'lines', a_L, 'exact value per side', (N - c) // q, '| sides', N + a_P + 2 * len(Pc),
      N + a_L + 2 * len(S1), 'order', 2 * N + a_P + a_L + 2 * c, flush=True)
lev = [-1] * (2 * N)
for p in A0P | set(U):
    lev[p] = 0
for k in A0L | set(W):
    lev[N + k] = 0
for k in S1:
    lev[N + k] = 1
for P in Pc:
    lev[P] = 1
tag = f'q{q}_r{len(best)}_s{seed}{"_exact" if exact else ""}'
(HERE / f'switch_{tag}.json').write_text(json.dumps({'q': q, 'blocks': best, 'S1': S1, 'centres_points': Pc,
                                                     'whiskers': W, 'dual': U}))
# m = 2 doubled graph: level -1 one version, level L 2^(L+1) versions; adjacent iff one string prefixes the other
nver = [1 if l < 0 else 2 ** (l + 1) for l in lev]
first = np.concatenate([[0], np.cumsum(nver)[:-1]]).tolist()
edges = []
for k, L in enumerate(lines):
    for p in L:
        a, b = p, N + k
        la, lb = lev[a], lev[b]
        if la > lb:
            a, b, la, lb = b, a, lb, la
        na = 1 if la < 0 else 2 ** (la + 1)
        ext = 1 if lb < 0 else 2 ** (lb + 1 - (la + 1 if la >= 0 else 0))
        for ia in range(na):
            for e2 in range(ext):
                ib = ia * ext + e2 if la >= 0 else e2
                edges.append((first[a] + ia, first[b] + ib))
n = sum(nver)
deg = np.bincount(np.array(edges).ravel(), minlength=n)
print('graph', n, 'vertices', len(edges), 'edges, max degree', deg.max())
out = HERE / 'graphs' / f'switch_{tag}_n{n}.txt'
out.write_text(f'{n}\n' + ''.join(f'{u} {v}\n' for u, v in edges))
print('wrote', out)

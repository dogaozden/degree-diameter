"""Delorme doubling on H(2) and H(3): checks the D = 6 lemma on the smallest hexagons.

S = a Hermitian spread (q^3+1 pairwise opposite lines: the lines of H(q) inside a suitable hyperplane).
Levels as in Delorme 1985, Sec. 8(b): one spread line v at level 2, its points at level 1, the other lines through
them at level 0; the other spread lines at level 1 and their points at level 0. Gain q^4+4q^3+q^2+4q+10.
Then 'whiskers' (single level): extra level-0 lines through points of S - v, disjoint off S, found by ILP.

python3 hex_small.py q SECONDS
"""
import itertools
import json
import sys
import time
import importlib.util
from collections import deque

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from lift import ROOT, lib

sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402

spec = importlib.util.spec_from_file_location('d6lift', ROOT / 'research' / 'p4' / 'd6' / 'lift.py')
d6lift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d6lift)

q, secs = int(sys.argv[1]), float(sys.argv[2])
N, lines = gh_build.hexagon(q)
P = gh_build.quadric_points(q)
assert len(P) == N
assert len(lines) == N
V = 2 * N
adj = [[] for _ in range(V)]
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        adj[p].append(N + k)
        adj[N + k].append(p)
        through[p].append(k)


def bfs(s):
    d = [-1] * V
    d[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                dq.append(y)
    return d


# Hermitian spread: a hyperplane containing exactly q^3+1 lines of H(q), pairwise opposite
S = None
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(c for c in a if c) != 1:
        continue
    inH = [sum(x * y for x, y in zip(a, v)) % q == 0 for v in P]
    cand = [k for k, L in enumerate(lines) if all(inH[p] for p in L)]
    if len(cand) != q ** 3 + 1:
        continue
    d0 = {k: bfs(N + k) for k in cand[:3]}
    if all(d0[k][N + j] == 6 for k in d0 for j in cand if j != k):
        if all(bfs(N + k)[N + j] == 6 for k in cand for j in cand if j != k):
            S, hyper = cand, a
            break
print(f'H({q}): {N} points, spread of {len(S)} lines from hyperplane {hyper}', flush=True)


def check(lev, tag):
    n, edges, _ = d6lift.build(V, adj, lev)
    ok = lib.is_valid(n, edges, q + 2, 6)
    print(f'  {tag}: order {n} (gain {n - V}), valid(Delta={q+2}, D=6) {ok}', flush=True)
    if ok:
        out = ROOT / 'research' / 'p4' / 'hats' / 'graphs' / f'hex_q{q}_{tag}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+2}D6', 'value': n, 'output': [n, [list(e) for e in edges]]}))
    return ok


# single level: stars on all spread lines
lev = [-1] * V
for s in S:
    lev[N + s] = 0
    for p in lines[s]:
        lev[p] = 0
check(lev, 'stars')
# Delorme levels
v = S[0]
lev = [-1] * V
for s in S[1:]:
    lev[N + s] = 1
    for p in lines[s]:
        lev[p] = 0
lev[N + v] = 2
for p in lines[v]:
    lev[p] = 1
    for k in through[p]:
        if k != v:
            lev[N + k] = 0
check(lev, 'delorme')
# whiskers by ILP: lines not in S and not through a point of v, with no off-S point on two whiskers or on a line
# through a point of v (those points already see a level-0 line).
Sset = set(S)
onS = set(p for s in S for p in lines[s])
vlines = set(k for p in lines[v] for k in through[p])
blocked = set(p for k in vlines for p in lines[k]) - onS
cand = [k for k in range(N) if k not in Sset and k not in vlines and not any(p in blocked for p in lines[k])]
offpts = sorted(set(p for k in cand for p in lines[k]) - onS)
idx = {p: i for i, p in enumerate(offpts)}
A = lil_matrix((len(offpts), len(cand)))
for j, k in enumerate(cand):
    for p in lines[k]:
        if p in idx:
            A[idx[p], j] = 1
t = time.time()
r = milp(-np.ones(len(cand)), constraints=[LinearConstraint(A.tocsr(), 0, 1)], integrality=np.ones(len(cand)),
         bounds=Bounds(0, 1), options={'time_limit': secs})
W = [cand[j] for j in range(len(cand)) if r.x[j] > 0.5]
print(f'  whiskers: {len(W)} (bound {-r.mip_dual_bound:.1f}, {r.message}, {time.time()-t:.0f}s)')
from collections import Counter
perpt = Counter(p for k in W for p in lines[k] if p in onS)
print('  whiskers per S-point (count of points with 0,1,..):',
      sorted(Counter(perpt.get(p, 0) for s in S[1:] for p in lines[s]).items()))
print('  S-lines by number of whiskered points:',
      sorted(Counter(sum(1 for p in lines[s] if perpt.get(p, 0)) for s in S[1:]).items()))
# unital structure on S: block B(p) = S-lines meeting a line through the off-S point p
Sidx = {N + s: s for s in S}
Sline_of = {p: s for s in S for p in lines[s]}
blocks = set()
for p in range(N):
    if p in onS:
        continue
    B = frozenset(Sline_of[[x for x in lines[k] if x in onS][0]] for k in through[p])
    blocks.add(B)
from itertools import combinations
pairs = Counter(pr for B in blocks for pr in combinations(sorted(B), 2))
print('  blocks:', len(blocks), 'sizes', set(map(len, blocks)), 'pair coverage', set(pairs.values()),
      'pairs', len(pairs), 'of', len(S) * (len(S) - 1) // 2)
empty = [s for s in S[1:] if not any(perpt.get(p, 0) for p in lines[s])]
thru_v = [B for B in blocks if v in B]
cov = [B for B in thru_v if (B - {v}) <= set(empty)]
print('  blocks through v:', len(thru_v), ' blocks through v inside empty+v:', len(cov))
json.dump({'q': q, 'S': S, 'v': v, 'whiskers': W, 'empty': empty},
          open(ROOT / 'research' / 'p4' / 'hats' / f'whiskers_q{q}.json', 'w'))
for k in W:
    lev[N + k] = 0
check(lev, f'delorme_whisk{len(W)}')

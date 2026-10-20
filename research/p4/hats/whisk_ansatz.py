"""Exact whisker sets with the ansatz seen at q = 2, 3.

H(q), Hermitian spread S (lines in a hyperplane), v in S. The blocks of the Hermitian unital on S are
B(p) = {S-lines met by the lines through p}, p off S. Choose q blocks through v; their S-lines (other than v) stay
empty, every point of every other S-line (other than v) gets exactly one whisker (a line through it opposite v), and
every free point (off S, at distance 5 from v) lies on exactly one whisker.

python3 whisk_ansatz.py q MODE SECONDS
  MODE = all       try every q-set of blocks through v (q = 2, 3), report which are feasible
  MODE = i,j,k,..  use these blocks through v (indices into the sorted list)
"""
import itertools
import json
import sys
import time
from collections import deque

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from lift import ROOT
sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402

q, mode, secs = int(sys.argv[1]), sys.argv[2], float(sys.argv[3])
hexfile = ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json'
if hexfile.exists():
    lines = json.loads(hexfile.read_text())['lines']
    N = len(lines)
else:
    N, lines = gh_build.hexagon(q)
P = gh_build.quadric_points(q)
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
# Hermitian spread: first hyperplane (in lexicographic order) holding q^3+1 lines (checked pairwise opposite below)
S = None
import os
hyps = [tuple(int(c) for c in os.environ['HYPER'].split(','))] if 'HYPER' in os.environ else \
    itertools.product(range(q), repeat=7)
for a in hyps:
    if not any(a) or next(c for c in a if c) != 1:
        continue
    inH = [sum(x * y for x, y in zip(a, w)) % q == 0 for w in P]
    cand = [k for k, L in enumerate(lines) if all(inH[p] for p in L)]
    if len(cand) == q ** 3 + 1:
        pts = [p for k in cand for p in lines[k]]
        if len(set(pts)) == len(pts):  # pairwise disjoint; opposite follows when no line meets two
            Sl = {p: k for k in cand for p in lines[k]}
            if all(len({Sl[x] for x in lines[k] if x in Sl}) <= 1 for k in range(N) if k not in set(cand)):
                S = cand
                break
v = S[0]
Sset = set(S)
Sline_of = {p: s for s in S for p in lines[s]}
V = 2 * N
dist = [-1] * V
dist[N + v] = 0
dq = deque([N + v])
while dq:
    x = dq.popleft()
    nb = through[x] if x < N else lines[x - N]
    for y in nb:
        y = N + y if x < N else y
        if dist[y] < 0:
            dist[y] = dist[x] + 1
            dq.append(y)
blocks = set()
for p in range(N):
    if p not in Sline_of:
        blocks.add(frozenset(Sline_of[[x for x in lines[k] if x in Sline_of][0]] for k in through[p]))
thru_v = sorted((sorted(B) for B in blocks if v in B))
free = [p for p in range(N) if p not in Sline_of and dist[p] == 5]
fidx = {p: i for i, p in enumerate(free)}
print(f'H({q}): S={len(S)}, blocks={len(blocks)}, through v={len(thru_v)}, free points={len(free)}', flush=True)


def solve(choice):
    E = set(s for i in choice for s in thru_v[i]) - {v}
    full_pts = [p for s in S if s != v and s not in E for p in lines[s]]
    cand = []
    for X in full_pts:
        for k in through[X]:
            if k not in Sset and dist[N + k] == 6:
                cand.append((X, k))
    A = lil_matrix((len(free) + len(full_pts), len(cand)))
    xi = {X: i for i, X in enumerate(full_pts)}
    for j, (X, k) in enumerate(cand):
        A[len(free) + xi[X], j] = 1
        for p in lines[k]:
            if p in fidx:
                A[fidx[p], j] = 1
    t = time.time()
    r = milp(np.zeros(len(cand)), constraints=[LinearConstraint(A.tocsr(), 1, 1)], integrality=np.ones(len(cand)),
             bounds=Bounds(0, 1), options={'time_limit': secs})
    ok = r.status == 0
    W = [cand[j][1] for j in range(len(cand)) if ok and r.x[j] > 0.5]
    return ok, r.message, W, time.time() - t


if mode == 'lines':  # q-sets of blocks through v met by every other block in at most 2 of them
    TV = [set(B) - {v} for B in thru_v]
    others = [B for B in blocks if v not in B]
    meet = [[i for i in range(len(TV)) if B & TV[i]] for B in others]
    good = []

    def ext(cur, start):
        if len(cur) == q:
            good.append(tuple(cur))
            return len(good) >= 3
        for i in range(start, len(TV)):
            c2 = cur + [i]
            if all(sum(1 for j in m if j in c2) <= 2 for m in meet):
                if ext(c2, i + 1):
                    return True
        return False
    ext([0], 1)
    print('q-sets through block 0 with every other block meeting <= 2:', good, flush=True)
    for choice in good[:1]:
        ok, msg, W, dt = solve(choice)
        print(choice, ok, msg, len(W), f'{dt:.0f}s', flush=True)
        if ok:
            out = ROOT / 'research' / 'p4' / 'hats' / f'whiskers_ansatz_q{q}.json'
            out.write_text(json.dumps({'q': q, 'S': S, 'v': v, 'whiskers': W, 'blocks_v': [thru_v[i] for i in choice]}))
            print('wrote', out)
elif mode == 'all':
    res = {}
    for choice in itertools.combinations(range(len(thru_v)), q):
        ok, msg, W, dt = solve(choice)
        res[choice] = ok
        print(choice, ok, f'{dt:.1f}s', flush=True)
    print('feasible:', sum(res.values()), 'of', len(res))
else:
    choice = [int(c) for c in mode.split(',')]
    ok, msg, W, dt = solve(choice)
    print(choice, ok, msg, len(W), f'{dt:.0f}s', flush=True)
    if ok:
        out = ROOT / 'research' / 'p4' / 'hats' / f'whiskers_ansatz_q{q}.json'
        out.write_text(json.dumps({'q': q, 'S': S, 'v': v, 'whiskers': W, 'blocks_v': [thru_v[i] for i in choice]}))
        print('wrote', out)

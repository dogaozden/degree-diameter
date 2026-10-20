"""Symmetric exact whisker sets on H(q) (q odd prime): impose invariance under a group K that fixes v, the
Hermitian spread S and the chosen blocks E.

Steps: root elements of G2(q) (g2_gens.py); v = a line fixed by 7 root subgroups; U_v = product of the 5 root
subgroups fixing v that are not a +-pair (the unipotent radical, order q^5); for every hyperplane through v that
gives a Hermitian spread S, K_S = Stab_{U_v}(S); choose q blocks through v (every other block meets <= 2 of them)
with the largest stabiliser K in K_S; then an ILP on K-orbits.

python3 whisk_sym.py q SECONDS
"""
import itertools
import json
import sys
import time
from collections import deque, Counter

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from g2_gens import Hex, fit, mat, LONG, SHORT
from lift import ROOT

q, secs = int(sys.argv[1]), float(sys.argv[2])
t0 = time.time()
H = Hex(q)
lines, P = H.lines, H.P
N = len(lines)
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
gens = fit(H)
assert all(c is not None for _, c in gens)
pats = [p for p, _ in gens]
coef = {p: c for p, c in gens}


def transpose(pat):
    return tuple(sorted((j, i) for i, j in pat))


neg = {p: next(r for r in pats if tuple(sorted(r)) == transpose(p)) for p in pats}
elem = {}
for p in pats:
    for t in range(1, q):
        M = mat(q, p, [t * c for c in coef[p]])
        pp = H.point_perm(M)
        elem[(p, t)] = (pp, H.line_perm(pp))
fixes = {p: [k for k in range(N) if elem[(p, 1)][1][k] == k] for p in pats}
cnt = Counter(k for p in pats for k in fixes[p])
v = max(cnt, key=lambda k: (cnt[k], -k))
fixv = [p for p in pats if v in fixes[p]]
levi = [p for p in fixv if neg[p] in fixv]
rad = [p for p in fixv if p not in levi]
print(f'H({q}) built; v={v} fixed by {len(fixv)} root groups, radical {len(rad)} ({time.time()-t0:.0f}s)', flush=True)
assert len(rad) == 5


def compose(a, b):  # first a then b
    return [b[x] for x in a]


ident_p, ident_l = list(range(N)), list(range(N))
U = [(ident_p, ident_l)]
for p in rad:
    new = []
    for (gp, gl) in U:
        new.append((gp, gl))
        for t in range(1, q):
            ep, el = elem[(p, t)]
            new.append((compose(gp, ep), compose(gl, el)))
    U = new
print(f'|U_v| = {len(U)}', flush=True)
# distances from v
V = 2 * N
dist = [-1] * V
dist[N + v] = 0
dq = deque([N + v])
while dq:
    x = dq.popleft()
    for y in (through[x] if x < N else lines[x - N]):
        y = N + y if x < N else y
        if dist[y] < 0:
            dist[y] = dist[x] + 1
            dq.append(y)
# hyperplanes through v giving Hermitian spreads
vv = [P[p] for p in lines[v][:2]]
best = None
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(c for c in a if c) != 1:
        continue
    if any(sum(x * y for x, y in zip(a, w)) % q for w in vv):
        continue
    inH = [sum(x * y for x, y in zip(a, w)) % q == 0 for w in P]
    Sc = [k for k in range(N) if all(inH[p] for p in lines[k])]
    if len(Sc) != q ** 3 + 1 or any(dist[N + k] != 6 for k in Sc if k != v):
        continue
    Sset = set(Sc)
    KS = [g for g in U if all(g[1][k] in Sset for k in Sc)]
    if best is None or len(KS) > len(best[2]):
        best = (a, Sc, KS)
    if len(KS) >= q ** 3:
        break
a, S, KS = best
Sset = set(S)
print(f'spread from hyperplane {a}: |K_S| = {len(KS)} ({time.time()-t0:.0f}s)', flush=True)
Sline_of = {p: s for s in S for p in lines[s]}
blocks = set()
for p in range(N):
    if p not in Sline_of:
        blocks.add(frozenset(Sline_of[[x for x in lines[k] if x in Sline_of][0]] for k in through[p]))
thru_v = sorted(sorted(B) for B in blocks if v in B)
TV = [frozenset(B) - {v} for B in thru_v]
others = [B for B in blocks if v not in B]
meet = [[i for i in range(len(TV)) if B & TV[i]] for B in others]
# all q-sets of blocks through v met by every other block in <= 2 (search containing block 0)
good = []


def ext(cur, start):
    if len(cur) == q:
        good.append(tuple(cur))
        return
    for i in range(start, len(TV)):
        c2 = cur + [i]
        if all(sum(1 for j in m if j in c2) <= 2 for m in meet):
            ext(c2, i + 1)


ext([0], 1)
print(f'{len(good)} good q-sets through block 0', flush=True)
bidx = {TV[i]: i for i in range(len(TV))}


def block_perm(g):
    return [bidx[frozenset(g[1][s] for s in TV[i])] for i in range(len(TV))]


bp = [block_perm(g) for g in KS]
choice, K = None, []
for c in good:
    cs = set(c)
    Kc = [g for g, b in zip(KS, bp) if {b[i] for i in c} == cs]
    if len(Kc) > len(K):
        choice, K = c, Kc
print(f'chosen blocks {choice}, |K| = {len(K)}', flush=True)
E = set().union(*[TV[i] for i in choice])
free = [p for p in range(N) if p not in Sline_of and dist[p] == 5]
full_pts = [p for s in S if s != v and s not in E for p in lines[s]]
cand = [(X, k) for X in full_pts for k in through[X] if k not in Sset and dist[N + k] == 6]
cid = {c: i for i, c in enumerate(cand)}
# orbits of K on candidates, X-points, free points
orb_c, seen = [], {}
for c in cand:
    if c in seen:
        continue
    o = {(g[0][c[0]], g[1][c[1]]) for g in K}
    for d in o:
        seen[d] = len(orb_c)
    orb_c.append(sorted(o))
orb_p = {}
for p in free:
    if p not in orb_p:
        for g in K:
            orb_p.setdefault(g[0][p], p)
reps = sorted(set(orb_p.values()))
xreps = sorted({min(g[0][X] for g in K) for X in full_pts})
print(f'orbits: {len(orb_c)} candidate, {len(reps)} free-point, {len(xreps)} X-point', flush=True)
A = lil_matrix((len(reps) + len(xreps), len(orb_c)))
ri = {p: i for i, p in enumerate(reps)}
xi = {X: len(reps) + i for i, X in enumerate(xreps)}
for j, o in enumerate(orb_c):
    for (X, k) in o:
        if X in xi:
            A[xi[X], j] += 1
        for p in lines[k]:
            if p in ri:
                A[ri[p], j] += 1
r = milp(np.zeros(len(orb_c)), constraints=[LinearConstraint(A.tocsr(), 1, 1)], integrality=np.ones(len(orb_c)),
         bounds=Bounds(0, 1), options={'time_limit': secs})
print('ILP:', r.message, flush=True)
if r.status == 0:
    W = sorted(k for j, o in enumerate(orb_c) if r.x[j] > 0.5 for (_, k) in o)
    cov = Counter(p for k in W for p in lines[k] if p in set(free))
    print(f'whiskers {len(W)}, distinct {len(set(W))}, free covered once: {len(cov) == len(free) and set(cov.values()) == {1}}')
    out = ROOT / 'research' / 'p4' / 'hats' / f'whiskers_sym_q{q}.json'
    out.write_text(json.dumps({'q': q, 'S': S, 'v': v, 'whiskers': W, 'hyperplane': a, 'blocks_v': [thru_v[i] for i in choice],
                               'K_order': len(K)}))
    print('wrote', out)

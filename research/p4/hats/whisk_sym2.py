"""Like whisk_sym.py, but numpy permutations (q = 7 fits), and the group K is enlarged by the diagonal torus
elements diag(a, b, c, 1, 1/a, 1/b, 1/c), abc = 1, that fix v, S and the chosen blocks.

python3 whisk_sym2.py q SECONDS [notorus]
"""
import itertools
import json
import sys
import time
from collections import deque, Counter

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from g2_gens import Hex, fit, mat
from lift import ROOT

q, secs = int(sys.argv[1]), float(sys.argv[2])
use_torus = not (len(sys.argv) > 3 and sys.argv[3] == 'notorus')
t0 = time.time()
H = Hex(q)
lines, P = H.lines, H.P
N = len(lines)
L = np.array(lines, dtype=np.int64)
through = [[] for _ in range(N)]
for k, Lk in enumerate(lines):
    for p in Lk:
        through[p].append(k)
gens = fit(H)
assert all(c is not None for _, c in gens)
pats = [p for p, _ in gens]
coef = {p: c for p, c in gens}
neg = {p: next(r for r in pats if tuple(sorted(r)) == tuple(sorted((j, i) for i, j in p))) for p in pats}


def perms_of(M):
    pp = H.point_perm(M)
    return np.array(pp), np.array(H.line_perm(pp))


elem = {(p, t): perms_of(mat(q, p, [t * c for c in coef[p]])) for p in pats for t in range(1, q)}
fixes = {p: set(np.nonzero(elem[(p, 1)][1] == np.arange(N))[0].tolist()) for p in pats}
cnt = Counter(k for p in pats for k in fixes[p])
v = max(cnt, key=lambda k: (cnt[k], -k))
fixv = [p for p in pats if v in fixes[p]]
rad = [p for p in fixv if neg[p] not in fixv]
assert len(rad) == 5
print(f'H({q}) ready, v={v} ({time.time()-t0:.0f}s)', flush=True)
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
ident = (np.arange(N), np.arange(N))


def U_elements():
    """All q^5 elements of the radical, as (point perm, line perm), generated lazily."""
    stack = [(0, ident)]
    while stack:
        i, g = stack.pop()
        if i == len(rad):
            yield g
            continue
        stack.append((i + 1, g))
        for t in range(1, q):
            ep, el = elem[(rad[i], t)]
            stack.append((i + 1, (ep[g[0]], el[g[1]])))


vv = [P[p] for p in lines[v][:2]]
best = None
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(c for c in a if c) != 1:
        continue
    if any(sum(x * y for x, y in zip(a, w)) % q for w in vv):
        continue
    inH = (np.array(P) @ np.array(a)) % q == 0
    Sc = np.nonzero(inH[L].all(axis=1))[0]
    if len(Sc) != q ** 3 + 1 or any(dist[N + k] != 6 for k in Sc if k != v):
        continue
    Smask = np.zeros(N, bool)
    Smask[Sc] = True
    KS = [g for g in U_elements() if Smask[g[1][Sc]].all()]
    print(f'  hyperplane {a}: |K_S| = {len(KS)}', flush=True)
    if best is None or len(KS) > len(best[2]):
        best = (a, Sc.tolist(), KS)
    if len(KS) >= q ** 3:
        break
a, S, KS = best
Sset = set(S)
print(f'spread {a}, |K_S| = {len(KS)} ({time.time()-t0:.0f}s)', flush=True)
Sline_of = {p: s for s in S for p in lines[s]}
blocks = set()
for p in range(N):
    if p not in Sline_of:
        blocks.add(frozenset(Sline_of[[x for x in lines[k] if x in Sline_of][0]] for k in through[p]))
thru_v = sorted(sorted(B) for B in blocks if v in B)
TV = [frozenset(B) - {v} for B in thru_v]
others = [B for B in blocks if v not in B]
meet = [[i for i in range(len(TV)) if B & TV[i]] for B in others]
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
bidx = {TV[i]: i for i in range(len(TV))}
rep_line = [min(T) for T in TV]  # a line of each block, to read block images
line_block = {s: i for i, T in enumerate(TV) for s in T}
bp = [[line_block[int(g[1][rep_line[i]])] for i in range(len(TV))] for g in KS]
choice, K = None, []
for c in good:
    cs = set(c)
    Kc = [g for g, b in zip(KS, bp) if {b[i] for i in c} == cs]
    if len(Kc) > len(K):
        choice, K = c, Kc
E = set().union(*[TV[i] for i in choice])
print(f'{len(good)} good q-sets; chosen {choice}, |K| = {len(K)}', flush=True)
gensK = list(K)
import os
torus_found = []
if use_torus:
    for x, y in itertools.product(range(1, q), repeat=2):
        z = pow(x * y, q - 2, q)
        D = np.diag([x, y, z, 1, pow(x, q - 2, q), pow(y, q - 2, q), pow(z, q - 2, q)]).astype(np.int64)
        gp, gl = perms_of(D)
        if gl[v] == v and all(int(gl[s]) in Sset for s in S) and all(int(gl[s]) in E for s in E):
            torus_found.append(((x, y, z), (gp, gl)))
    print('torus elements fixing v, S, E:', [t for t, _ in torus_found], flush=True)
    pick = os.environ.get('TORUS', 'all' if 'TORUSVAL' not in os.environ else 'none')
    for i, (t, g) in enumerate(torus_found):
        if pick == 'all' or str(i) in pick.split(',') or os.environ.get('TORUSVAL') == ','.join(map(str, t)):
            gensK.append(g)
# closure
key = lambda g: g[1].tobytes() + g[0].tobytes()
group = {key(ident): ident}
frontier = [ident]
while frontier:
    nf = []
    for g in frontier:
        for h in gensK:
            gh = (h[0][g[0]], h[1][g[1]])
            kk = key(gh)
            if kk not in group:
                group[kk] = gh
                nf.append(gh)
    frontier = nf
G = list(group.values())
print(f'group order {len(G)} (K {len(K)}, with torus: {use_torus}) ({time.time()-t0:.0f}s)', flush=True)
free = [p for p in range(N) if p not in Sline_of and dist[p] == 5]
freeset = set(free)
full_pts = [p for s in S if s != v and s not in E for p in lines[s]]
cand = [(X, k) for X in full_pts for k in through[X] if k not in Sset and dist[N + k] == 6]
seen, orb_c = {}, []
for c in cand:
    if c in seen:
        continue
    o = {(int(g[0][c[0]]), int(g[1][c[1]])) for g in G}
    for d in o:
        seen[d] = len(orb_c)
    orb_c.append(sorted(o))
rep_p = {}
for p in free:
    if p not in rep_p:
        for g in G:
            rep_p.setdefault(int(g[0][p]), p)
reps = sorted(set(rep_p.values()))
rep_x = {}
for X in full_pts:
    if X not in rep_x:
        for g in G:
            rep_x.setdefault(int(g[0][X]), X)
xreps = sorted(set(rep_x.values()))
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
if os.environ.get('SHOWRED'):
    xo = {X: i for i, X in enumerate(xreps)}
    opt = {}
    for j, o in enumerate(orb_c):
        X0 = [X for (X, k) in o if X in xi]
        cov = sorted(ri[p] for (X, k) in o for p in lines[k] if p in ri)
        opt.setdefault(xo[X0[0]], []).append((j, cov))
    for i in sorted(opt):
        print('X-orbit', i, ':', [c for _, c in opt[i]])
    cnt = Counter(f for i in opt for _, c in opt[i] for f in set(c))
    print('free orbit coverage multiplicities:', sorted(Counter(cnt.values()).items()))
    who = {}
    for i in opt:
        for jj, (_, c) in enumerate(opt[i]):
            for f in c:
                who.setdefault(f, []).append((i, jj))
    print('X-orbits per free orbit:', sorted(Counter(len({i for i, _ in w}) for w in who.values()).items()))
r = milp(np.zeros(len(orb_c)), constraints=[LinearConstraint(A.tocsr(), 1, 1)], integrality=np.ones(len(orb_c)),
         bounds=Bounds(0, 1), options={'time_limit': secs})
print('ILP:', r.message, flush=True)
if r.status == 0:
    W = sorted(k for j, o in enumerate(orb_c) if r.x[j] > 0.5 for (_, k) in o)
    cov = Counter(p for k in W for p in lines[k] if p in freeset)
    ok = len(cov) == len(free) and set(cov.values()) == {1} and len(set(W)) == len(W) == q * q * (q * q - 1)
    print(f'whiskers {len(W)}, exact: {ok}', flush=True)
    out = ROOT / 'research' / 'p4' / 'hats' / f'whiskers_sym2_q{q}.json'
    out.write_text(json.dumps({'q': q, 'S': S, 'v': v, 'whiskers': W, 'hyperplane': list(a),
                               'blocks_v': [thru_v[i] for i in choice], 'group_order': len(G),
                               'orbits_chosen': [orb_c[j] for j in range(len(orb_c)) if r.x[j] > 0.5]}))
    print('wrote', out)

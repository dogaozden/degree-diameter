"""Card c3 (conics-r2): check the self-polar doubling of H(3) from research/synthetic/CONICS.md section 3.2.

(1) H(3): 364 points, 364 lines, 4 per line, 4 per point, girth 12, diameter 6.
(2) A polarity theta (side-swapping involutive automorphism of the incidence graph, found with pynauty and
    random products of its generators). Absolute points O: 28 pairwise opposite; absolute lines S = theta(O):
    28 pairwise opposite; each absolute point on exactly one absolute line.
(3) One-level doubling with m = 2 on A0 = O u S, theta extended to versions, then the fold.
Writes result.json next to this file and prints it.
"""
import json
import os
import random
import sys
from collections import deque

import numpy as np
import pynauty

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from hexagon import incidence_graph  # noqa: E402

Q = 3
N, L, lines, adj = incidence_graph(Q)
V = N + L
adjset = [set(a) for a in adj]
res = {'q': Q, 'points': N, 'lines': L}


def bfs(adjl, s):
    d = [-1] * len(adjl)
    d[s] = 0
    dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adjl[u]:
            if d[w] < 0:
                d[w] = d[u] + 1
                dq.append(w)
    return d


def dist_matrix(adjl):
    return np.array([bfs(adjl, s) for s in range(len(adjl))])


def girth(adjl):
    best = 10 ** 9
    n = len(adjl)
    for s in range(n):
        d = [-1] * n
        par = [-1] * n
        d[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adjl[u]:
                if d[w] < 0:
                    d[w] = d[u] + 1
                    par[w] = u
                    dq.append(w)
                elif par[u] != w:
                    best = min(best, d[u] + d[w] + 1)
    return best


def is_aut(p, adjl, adjs):
    """p maps edges to edges (p is a permutation of range(len(adjl)))."""
    for u in range(len(adjl)):
        pu = p[u]
        for w in adjl[u]:
            if p[w] not in adjs[pu]:
                return False
    return True


def is_involution(p):
    return bool(np.array_equal(p[p], np.arange(len(p))))


def side_swap(p):
    return bool(np.all(p[:N] >= N)) and bool(np.all(p[N:] < N))


def compose(a, b):
    """x -> a[b[x]]: apply b first, then a."""
    return a[b]


def inverse(p):
    inv = np.empty_like(p)
    inv[p] = np.arange(len(p))
    return inv


def order(p):
    ident = np.arange(len(p))
    cur = p.copy()
    n = 1
    while not np.array_equal(cur, ident):
        cur = compose(p, cur)
        n += 1
    return n


def power(p, k):
    out = np.arange(len(p))
    base = p.copy()
    while k:
        if k & 1:
            out = compose(base, out)
        base = compose(base, base)
        k >>= 1
    return out


# ---------------- (1) hexagon checks ----------------
D0 = dist_matrix(adj)
check1 = {
    'point_count_364': N == 364,
    'line_count_364': L == 364,
    'four_points_per_line': all(len(l) == 4 for l in lines),
    'four_lines_per_point': all(len(adj[p]) == 4 for p in range(N)),
    'four_points_per_line_graph': all(len(adj[v]) == 4 for v in range(N, V)),
    'connected': bool((D0 >= 0).all()),
}
res['girth'] = girth(adj)
res['diameter_H3'] = int(D0.max())
check1['girth_12'] = res['girth'] == 12
check1['diameter_6'] = res['diameter_H3'] == 6
res['check1'] = check1
pass1 = all(check1.values())

# ---------------- (2) polarity search ----------------
G = pynauty.Graph(V, directed=False, adjacency_dict={v: adj[v] for v in range(V)})
gens, g1, g2, orbits, norb = pynauty.autgrp(G)
gens = [np.array(g, dtype=np.int64) for g in gens]
res['aut_group_order'] = f'{g1:.6g} * 10^{g2}'
res['aut_generators'] = len(gens)
assert all(is_aut(g, adj, adjset) for g in gens), 'pynauty generator is not an automorphism'

rng = random.Random(20261029)
slots = list(gens)
while len(slots) < 8:
    slots.append(compose(rng.choice(gens), rng.choice(gens)))


def step():
    i, j = rng.sample(range(len(slots)), 2)
    if rng.random() < 0.5:
        slots[i] = compose(slots[i], slots[j])
    else:
        slots[i] = compose(slots[i], inverse(slots[j]))
    return slots[i]


for _ in range(300):
    step()

def polarity_summary(th):
    absP = [x for x in range(N) if int(th[x]) in adjset[x]]
    absL = [N + k for k in range(L) if int(th[N + k]) in adjset[N + k]]
    return absP, absL


def opposite_check(vs):
    if len(vs) < 2:
        return False
    sub = D0[np.ix_(vs, vs)]
    off = sub[~np.eye(len(vs), dtype=bool)]
    return bool((off == 6).all())


polarities = []
tries = 0
seen_counts = []
while tries < 40000 and len(polarities) < 4:
    g = step()
    tries += 1
    if not side_swap(g):
        continue
    n = order(g)
    if n % 4 != 2:
        continue
    th = power(g, n // 2)  # involution; a duality because n/2 is odd
    if not (side_swap(th) and is_involution(th) and is_aut(th, adj, adjset)):
        continue
    absP, absL = polarity_summary(th)
    seen_counts.append((len(absP), len(absL)))
    polarities.append((th, absP, absL))

res['polarity_candidates_found'] = len(polarities)
res['polarity_tries'] = tries
res['absolute_counts_found'] = seen_counts

theta = None
absP = absL = None
for th, aP, aL in polarities:
    if len(aP) == 28 and len(aL) == 28:
        theta, absP, absL = th, aP, aL
        break
if theta is None and polarities:
    theta, absP, absL = polarities[0]

check2 = {'polarity_found': theta is not None}
if theta is not None:
    absPset, absLset = set(absP), set(absL)
    check2['involution'] = is_involution(theta)
    check2['side_swapping_automorphism'] = side_swap(theta) and is_aut(theta, adj, adjset)
    check2['absolute_points_28'] = len(absP) == 28
    check2['absolute_lines_28'] = len(absL) == 28
    check2['absolute_points_pairwise_opposite'] = opposite_check(absP)
    check2['absolute_lines_pairwise_opposite'] = opposite_check(absL)
    check2['absolute_lines_are_theta_of_O'] = set(int(theta[p]) for p in absP) == absLset
    check2['each_absolute_point_on_exactly_one_absolute_line'] = all(
        sum(1 for l in adj[p] if l in absLset) == 1 for p in absP)
    res['absolute_points'] = absP
    res['absolute_lines'] = absL
    res['theta_points_to_lines'] = [int(theta[p]) for p in range(N)]
else:
    check2['absolute_points_28'] = False
res['check2'] = check2
pass2 = all(check2.values())

# ---------------- (3) doubling, theta on versions, fold ----------------
pass3 = False
check3 = {}
if theta is not None:
    A0 = set(absP) | set(absL)
    res['A0_size'] = len(A0)

    def versions(v):
        return (1, 2) if v in A0 else (0,)

    keys = [(v, w) for v in range(V) for w in versions(v)]
    kid = {k: i for i, k in enumerate(keys)}
    NV = len(keys)
    dadj = [[] for _ in range(NV)]
    for x in range(N):
        for y in adj[x]:
            for w in versions(x):
                for u in versions(y):
                    if x in A0 and y in A0 and w != u:
                        continue
                    a, b = kid[(x, w)], kid[(y, u)]
                    dadj[a].append(b)
                    dadj[b].append(a)
    dadjs = [set(a) for a in dadj]
    degs = [len(a) for a in dadj]
    D3 = dist_matrix(dadj)
    res['doubled_elements'] = NV
    res['doubled_max_degree'] = max(degs)
    res['doubled_diameter'] = int(D3.max()) if (D3 >= 0).all() else None
    check3['elements_784'] = NV == 784
    check3['max_degree_5'] = max(degs) == 5
    check3['diameter_6'] = res['doubled_diameter'] == 6

    # theta on versions: (v, w) -> (theta(v), w)
    thp = np.array([kid[(int(theta[v]), w)] for (v, w) in keys], dtype=np.int64)
    check3['theta_prime_involution'] = is_involution(thp)
    check3['theta_prime_side_swapping'] = all(
        (thp[a] >= 0) and ((keys[a][0] < N) != (keys[int(thp[a])][0] < N)) for a in range(NV))
    check3['theta_prime_automorphism'] = is_aut(thp, dadj, dadjs)
    check3['theta_prime_is_polarity'] = (check3['theta_prime_involution'] and check3['theta_prime_side_swapping']
                                         and check3['theta_prime_automorphism'])

    # fold: points only (keys with v < N), p ~ r iff p != r and p on theta'(r)
    pts = [a for a in range(NV) if keys[a][0] < N]
    fidx = {r: i for i, r in enumerate(pts)}
    fold = [set() for _ in pts]
    for r in pts:
        for p in dadj[int(thp[r])]:
            if p != r and keys[p][0] < N:
                fold[fidx[r]].add(fidx[p])
    sym = all(r in fold[p] for r in range(len(pts)) for p in fold[r])
    fadj = [sorted(s) for s in fold]
    FD = dist_matrix(fadj)
    fdeg = [len(s) for s in fold]
    res['fold_vertices'] = len(pts)
    res['fold_max_degree'] = max(fdeg)
    res['fold_diameter'] = int(FD.max()) if (FD >= 0).all() else None
    check3['fold_symmetric'] = sym
    check3['fold_392_vertices'] = len(pts) == 392
    check3['fold_max_degree_le_5'] = max(fdeg) <= 5
    check3['fold_diameter_le_5'] = res['fold_diameter'] is not None and res['fold_diameter'] <= 5
    pass3 = all(check3.values())
res['check3'] = check3

score = int(pass1) + int(pass2) + int(pass3)
res['pass'] = {'check1_hexagon': pass1, 'check2_polarity': pass2, 'check3_doubling_fold': pass3}
res['score'] = score
res['valid'] = score == 3

out = os.path.join(HERE, 'result.json')
with open(out, 'w') as f:
    json.dump(res, f, indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
print(json.dumps({k: v for k, v in res.items() if k not in ('absolute_points', 'absolute_lines', 'theta_points_to_lines')},
                 default=lambda o: o.item() if hasattr(o, 'item') else str(o), indent=1))

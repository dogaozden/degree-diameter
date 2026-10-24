#!/usr/bin/env python3
"""gq3.py: the symplectic generalized quadrangle W(3) as a hub graph for d7hex (mode 3), card c1, exp2 round 1.

Points: the 40 points of PG(3,3) (1-dim subspaces, normalised so the first nonzero coordinate is 1).
Lines: the 40 totally isotropic 2-dim subspaces of B(x,y) = x0*y1 - x1*y0 + x2*y3 - x3*y2 (mod 3).

Writes w3.hg: "40 160", then one line "j k" per incidence (GQ point j on GQ line k), with line-side hub j = point j
and point-side hub k = line k. Also writes induced subgraphs on the first K points and first K lines
(w3_K30.hg, w3_K20.hg) if all same-side hub distances inside that hub graph are <= 6.
"""
import itertools
from collections import deque

P = 3
MAXD = 6  # required same-side hub distance


def B(x, y):
    return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % P


def normalize(v):
    for c in v:
        if c % P:
            inv = 1 if c % P == 1 else 2  # inverses mod 3: 1 -> 1, 2 -> 2
            return tuple((x * inv) % P for x in v)
    return None


def span_points(a, b):
    s = set()
    for x in range(P):
        for y in range(P):
            if x or y:
                s.add(normalize(tuple((x * a[i] + y * b[i]) % P for i in range(4))))
    return frozenset(s)


def build():
    vecs = [v for v in itertools.product(range(P), repeat=4) if any(v)]
    points = sorted({normalize(v) for v in vecs})
    assert len(points) == 40, len(points)
    pidx = {p: i for i, p in enumerate(points)}
    lines = set()
    for i, a in enumerate(points):
        for b in points[i + 1:]:
            if B(a, b) == 0:
                lines.add(span_points(a, b))
    lines_idx = sorted((sorted(pidx[p] for p in L) for L in lines), key=lambda L: L)
    return points, lines_idx


def check_gq(npts, lines_idx):
    assert len(lines_idx) == 40, len(lines_idx)
    assert all(len(L) == 4 for L in lines_idx), "line size"
    on = [[] for _ in range(npts)]
    for k, L in enumerate(lines_idx):
        for j in L:
            on[j].append(k)
    assert all(len(x) == 4 for x in on), "point degree"
    coll = [set() for _ in range(npts)]
    for L in lines_idx:
        for a in L:
            for b in L:
                if a != b:
                    coll[a].add(b)
    # GQ axiom: a point off a line is collinear with exactly one point of the line
    for L in lines_idx:
        Ls = set(L)
        for x in range(npts):
            if x not in Ls:
                assert len(coll[x] & Ls) == 1, "GQ axiom"
    # incidence graph: points 0..39, lines 40..79
    adj = [[] for _ in range(npts + len(lines_idx))]
    for k, L in enumerate(lines_idx):
        for j in L:
            adj[j].append(npts + k)
            adj[npts + k].append(j)
    diam = 0
    for s in range(len(adj)):
        d = [-1] * len(adj)
        d[s] = 0
        dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if d[w] < 0:
                    d[w] = d[v] + 1
                    dq.append(w)
        assert min(d) >= 0, "disconnected"
        diam = max(diam, max(d))
    return diam


def same_side_max(K, edges):
    """Max distance between same-side hubs inside the hub graph on hubs 0..K-1 (None if disconnected)."""
    adj = {('j', j): [] for j in range(K)}
    adj.update({('k', k): [] for k in range(K)})
    for j, k in edges:
        adj[('j', j)].append(('k', k))
        adj[('k', k)].append(('j', j))
    worst = 0
    for side in 'jk':
        for s in range(K):
            d = {('j', s) if side == 'j' else ('k', s): 0}
            dq = deque(d)
            while dq:
                v = dq.popleft()
                for w in adj[v]:
                    if w not in d:
                        d[w] = d[v] + 1
                        dq.append(w)
            for t in range(K):
                key = (side, t)
                if key == (side, s):
                    continue
                if key not in d:
                    return None
                worst = max(worst, d[key])
    return worst


def write_hg(path, K, edges):
    with open(path, 'w') as f:
        f.write(f"{K} {len(edges)}\n")
        for j, k in edges:
            f.write(f"{j} {k}\n")


def main():
    points, lines_idx = build()
    diam = check_gq(len(points), lines_idx)
    edges = [(j, k) for k, L in enumerate(lines_idx) for j in L]
    edges.sort()
    print(f"points {len(points)}, lines {len(lines_idx)}, incidences {len(edges)}, "
          f"incidence-graph diameter {diam} (GQ axioms checked)")
    worst = same_side_max(40, edges)
    print(f"W(3) hub graph: max same-side hub distance {worst}, hub degrees "
          f"{min(len(L) for L in lines_idx)} (lines) / 4 (points)")
    write_hg("w3.hg", 40, edges)
    print("wrote w3.hg: K=40, m=%d" % len(edges))
    for K in (30, 20):
        sub = [(j, k) for (j, k) in edges if j < K and k < K]
        w = same_side_max(K, sub)
        if w is None or w > MAXD:
            print(f"induced K={K}: same-side hub distance {w}: rejected (needs <= {MAXD})")
        else:
            write_hg(f"w3_K{K}.hg", K, sub)
            print(f"induced K={K}: m={len(sub)}, max same-side hub distance {w}: wrote w3_K{K}.hg")


if __name__ == "__main__":
    main()

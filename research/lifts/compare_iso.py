"""Isomorphism test between a lift (edge list written by verify_lift.py) and a published graph.

Usage: python3 -I compare_iso.py EDGES ADJLIST
ADJLIST: Hafner's format (row i lists the neighbours of vertex i; labels 0- or 1-based, detected; '#' = comment).
Prints n, degrees, diameter, the adjacency spectrum comparison, and the verdict of an exact backtracking search:
fix a vertex a0 of the lift, try every image b of the published graph, extend along a BFS order of the lift
(each new vertex goes to an unused neighbour of its parent's image, adjacency to all mapped vertices checked).
The search is complete, so "not isomorphic" is a proof (given the spectra it is usually decided at once).
"""
import sys
from collections import deque

import numpy as np


def read_edges(fn):
    with open(fn) as f:
        n = int(f.readline())
        adj = [set() for _ in range(n)]
        for line in f:
            u, v = map(int, line.split())
            adj[u].add(v)
            adj[v].add(u)
    return adj


def read_adj(fn):
    rows = [list(map(int, l.split())) for l in open(fn) if l.strip() and not l.lstrip().startswith("#")]
    n = len(rows)
    one = max(max(r) for r in rows) == n   # 1-based labels if the label n occurs, else 0-based
    adj = [set() for _ in range(n)]
    for i, r in enumerate(rows):
        for w in r:
            j = w - 1 if one else w
            adj[i].add(j)
            adj[j].add(i)
    return adj


def ecc(adj, s):
    d = [-1] * len(adj)
    d[s] = 0
    q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0:
                d[w] = d[u] + 1
                q.append(w)
    return d


def spectrum(adj):
    n = len(adj)
    M = np.zeros((n, n))
    for u in range(n):
        for w in adj[u]:
            M[u, w] = 1
    return np.sort(np.linalg.eigvalsh(M))


def find_iso(A, B):
    n = len(A)
    d0 = ecc(A, 0)
    order = sorted(range(n), key=lambda v: d0[v])
    parent = {}
    for v in order[1:]:
        parent[v] = min(u for u in A[v] if d0[u] == d0[v] - 1)
    pos = {v: i for i, v in enumerate(order)}
    sys.setrecursionlimit(10000)
    for b in range(len(B)):
        dB = ecc(B, b)
        if sorted(dB) != sorted(d0):
            continue
        f = {0: b}
        used = {b}

        def ext(i):
            if i == n:
                return True
            v = order[i]
            back = [u for u in A[v] if pos[u] < i]
            for c in B[f[parent[v]]]:
                if c in used or len(B[c]) != len(A[v]) or dB[c] != d0[v]:
                    continue
                if all(f[u] in B[c] for u in back) and sum(1 for w in B[c] if w in used) == len(back):
                    f[v] = c
                    used.add(c)
                    if ext(i + 1):
                        return True
                    del f[v]
                    used.discard(c)
            return False

        if ext(1):
            return f
    return None


def main():
    A, B = read_edges(sys.argv[1]), read_adj(sys.argv[2])
    for name, G in (("lift", A), ("published", B)):
        degs = sorted(set(len(a) for a in G))
        diam = max(max(ecc(G, s)) for s in range(len(G)))
        print(f"{name}: n={len(G)} edges={sum(len(a) for a in G) // 2} degrees={degs} diameter={diam}", flush=True)
    if len(A) != len(B):
        print("NOT ISOMORPHIC (orders differ)")
        return
    sa, sb = spectrum(A), spectrum(B)
    same = np.allclose(sa, sb, atol=1e-6)
    print(f"adjacency spectra equal: {same}", flush=True)
    if not same:
        print("NOT ISOMORPHIC (spectra differ)")
        return
    f = find_iso(A, B)
    if f is None:
        print("NOT ISOMORPHIC (exhaustive backtracking)")
    else:
        ok = all(f[w] in B[f[v]] for v in range(len(A)) for w in A[v])
        print(f"ISOMORPHIC (explicit map found, edge check {ok})")


if __name__ == "__main__":
    main()

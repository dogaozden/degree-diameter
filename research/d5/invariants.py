"""Invariants of the D=5 record graphs: degrees per side, girth, distance profile,
short-cycle counts, spectrum, automorphism group (pynauty) and its orbits.

Usage: python3 invariants.py GRAPH.json [...]
"""
import json
import sys
from collections import Counter, deque

import numpy as np
import pynauty


def load(path):
    d = json.load(open(path))
    n, edges = d["output"]
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return n, adj


def sides(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0:
            continue
        col[s] = 0
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if col[y] < 0:
                    col[y] = 1 - col[x]
                    dq.append(y)
    return col


def bfs(adj, s):
    dist = [-1] * len(adj)
    dist[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                dq.append(y)
    return dist


def girth_at(adj, s):
    """Shortest cycle through s (bipartite: even)."""
    dist = [-1] * len(adj)
    par = [-1] * len(adj)
    dist[s] = 0
    dq = deque([s])
    best = 10**9
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                par[y] = x
                dq.append(y)
            elif par[x] != y:
                best = min(best, dist[x] + dist[y] + 1)
    return best


def main(path):
    n, adj = load(path)
    col = sides(n, adj)
    print(f"== {path}\nn={n}  edges={sum(map(len, adj))//2}")
    for c in (0, 1):
        print(f" side {c}: {col.count(c)} vertices, degrees {sorted(Counter(len(adj[v]) for v in range(n) if col[v]==c).items())}")
    A = np.zeros((n, n))
    for u in range(n):
        for v in adj[u]:
            A[u, v] = 1
    A2 = A @ A
    c4 = (np.sum(A2 * A2) - np.sum(np.diag(A2) ** 2) - np.sum(np.diag(A2)) + np.sum(np.diag(A2))) / 8
    # number of 4-cycles = (sum_{u!=v} C(A2[u,v],2)) / 4  (each 4-cycle counted by 2 diagonal pairs x 2 orders)
    off = A2.copy()
    np.fill_diagonal(off, 0)
    c4 = np.sum(off * (off - 1) / 2) / 4
    print(f" 4-cycles: {int(round(c4))}")
    g = min(girth_at(adj, s) for s in range(n))
    print(f" girth: {g}")
    ecc = Counter()
    prof = Counter()
    for s in range(n):
        d = bfs(adj, s)
        ecc[max(d)] += 1
        prof[tuple(Counter(d)[k] for k in range(max(d) + 1))] += 1
    print(f" eccentricities: {dict(ecc)}")
    print(f" distinct distance profiles: {len(prof)}; most common: {prof.most_common(4)}")
    ev = np.round(np.linalg.eigvalsh(A), 4)
    evc = Counter(ev)
    print(f" distinct eigenvalues: {len(evc)}; top: {sorted(evc.items(), reverse=True)[:12]}")
    G = pynauty.Graph(n, adjacency_dict={v: list(adj[v]) for v in range(n)})
    gens, grpsize1, grpsize2, orbits, norb = pynauty.autgrp(G)
    print(f" |Aut| = {grpsize1:.6g} * 10^{grpsize2}; orbits: {norb}; orbit sizes {sorted(Counter(Counter(orbits).values()).items())}")
    return n, adj, col, gens, orbits


if __name__ == "__main__":
    for p in sys.argv[1:]:
        main(p)

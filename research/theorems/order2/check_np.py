#!/usr/bin/env python3
"""check_np.py: independent diameter check of a haar_gen3-format solution file, on the group code of hgroups.py
(written for this job, sharing nothing with haar_gen3/haar_sym or build_haar2.py).

Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B).  Right multiplication by G is an automorphism group
transitive on each side, so the diameter is max(ecc(e,A), ecc(e,B)).  Checks: |S| = d distinct elements (so no repeated
edges and every vertex has degree d), ecc from (e,A) and from (e,B) by full BFS over all 2N vertices, everything reached.
Usage: check_np.py SOLUTION.txt"""
import sys, time, hashlib
import numpy as np
from hgroups import read_solution


def bfs(G, L, Li, startB, N):
    """distances (in steps) from (e, side) to every vertex; returns (dA, dB) arrays (-1 = unreached)"""
    dist = [np.full(N, -1, np.int16), np.full(N, -1, np.int16)]
    side = 1 if startB else 0
    dist[side][G.ident] = 0
    frontier = np.array([G.ident])
    step = 0
    while len(frontier):
        step += 1
        ns = side ^ 1
        T = L if side == 0 else Li            # A -> B: g -> s g ;  B -> A: g -> s^-1 g
        nxt = np.unique(np.concatenate([t[frontier] for t in T]))
        nxt = nxt[dist[ns][nxt] < 0]
        dist[ns][nxt] = step
        frontier, side = nxt, ns
    return dist


def main():
    t0 = time.time()
    d, D, G, S = read_solution(sys.argv[1])
    N = G.N
    print(f"group {G.spec}, N = {N}, vertices {2 * N}, d = {d}, D = {D}")
    ok = True
    if len(set(S)) != d:
        print("FAIL: repeated generators"); ok = False
    L = [G.left_perm(s) for s in S]
    for t in L:
        assert len(np.unique(t)) == N
    Li = []
    for t in L:
        q = np.empty_like(t); q[t] = np.arange(N); Li.append(q)
    eccs = []
    for startB in (False, True):
        dA, dB = bfs(G, L, Li, startB, N)
        unreached = int((dA < 0).sum() + (dB < 0).sum())
        ecc = int(max(dA.max(), dB.max()))
        eccs.append(ecc)
        print(f"ecc from (e,{'B' if startB else 'A'}) = {ecc}, unreached {unreached}")
        if unreached:
            ok = False
    edges_hash = hashlib.sha256()
    for i, t in enumerate(L):                 # edge list in a fixed order: for each generator, A-index g -> B-index s g
        edges_hash.update(t.astype(np.int64).tobytes())
    print(f"edge-table sha256 (this script's own indexing) = {edges_hash.hexdigest()}")
    diam = max(eccs)
    if ok and diam <= D:
        print(f"VALID d={d} D={D} group={G.spec} N={N} vertices={2 * N} diameter={diam}  ({time.time() - t0:.0f} s)")
    else:
        print(f"INVALID (diameter {diam})")


if __name__ == "__main__":
    main()

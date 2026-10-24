#!/usr/bin/env python3
"""Independent check of ctrl_exh's NB-4 coverage: build the Haar controller H(G,S) (A-vertex i ~ B-vertex T[i][s], s in S)
from a multiplication table and count same-side pairs NOT joined by a nonbacktracking walk of length 4."""
import sys, subprocess
def load(path):
    with open(path) as f:
        m = int(f.readline()); T = [list(map(int, f.readline().split())) for _ in range(m)]
    return m, T
def uncovered(m, T, S):
    # edges: A-vertex i -- B-vertex j, j = T[i][s]; A-side vertex index i, B-side index j (both 0..m-1)
    adjA = [[T[i][s] for s in S] for i in range(m)]           # A -> B
    inv = {}
    adjB = [[] for _ in range(m)]                               # B -> A
    for i in range(m):
        for j in adjA[i]:
            adjB[j].append(i)
    def nb_reach(start, side):
        # NB walks of length 4 from start (on side), returns endpoints on the same side
        def step(v, prev, sd):
            if sd == 'A': return [(j, 'B') for j in adjA[v] if (prev is None or j != prev)]
            return [(i, 'A') for i in adjB[v] if (prev is None or i != prev)]
        frontier = [(start, None, side)]
        for _ in range(4):
            nxt = []
            for v, prev, sd in frontier:
                for w, sw in step(v, prev, sd):
                    nxt.append((w, v, sw))
            frontier = nxt
        return set(v for v, _, sd in frontier if sd == side)
    unc = {}
    for side in ('A', 'B'):
        n_unc = 0
        for u in range(m):
            R = nb_reach(u, side)
            n_unc += m - len(R)
        unc[side] = n_unc
    return unc

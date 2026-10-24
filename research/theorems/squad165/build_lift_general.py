#!/usr/bin/env python3
"""Route-chart lift of a general 4-regular bipartite controller (edge list "a b", a, b in 0..m-1: A-vertex a --
B-vertex b; 4m lines).  The controller is properly 4-edge-coloured (Konig: peel off perfect matchings), colour c
gets chart letter c: (a, x)_A -- (b, A_c x + lam b_c)_B.  Every nonbacktracking walk then has consecutive distinct
letters, so a universal chart (chart_u1.json) makes every NB walk of length 4 nonsingular.
usage: python3 build_lift_general.py controller.edges chart.json out.edges"""
import sys, json, itertools
from chart import mat_vec, MUL, vid

def perfect_matching(m, adj):
    """adj: list of lists A->B (multigraph allowed). Hopcroft-Karp-lite (augmenting paths)."""
    matchB = [-1] * m
    def try_(a, seen):
        for b in adj[a]:
            if b in seen: continue
            seen.add(b)
            if matchB[b] < 0 or try_(matchB[b], seen):
                matchB[b] = a; return True
        return False
    for a in range(m):
        if not try_(a, set()):
            raise RuntimeError('no perfect matching')
    return {matchB[b]: b for b in range(m)}

def colour(m, edges):
    adj = [[] for _ in range(m)]
    for a, b in edges: adj[a].append(b)
    out = []
    for c in range(4):
        M = perfect_matching(m, adj)
        for a, b in M.items():
            out.append((a, b, c)); adj[a].remove(b)
    return out

if __name__ == '__main__':
    edges = [tuple(map(int, l.split()[:2])) for l in open(sys.argv[1]) if l.strip()]
    m = max(a for a, b in edges) + 1
    assert len(edges) == 4 * m
    ch = json.load(open(sys.argv[2])); A = ch['A']; bv = [tuple(v) for v in ch['b']]
    col = colour(m, edges)
    vecs = list(itertools.product(range(4), repeat=4)); nA = m * 256
    E = []
    for a, b, c in col:
        for x in vecs:
            y0 = mat_vec(A[c], x)
            for lam in range(4):
                y = tuple(p ^ MUL[lam][q] for p, q in zip(y0, bv[c]))
                E.append((a * 256 + vid(x), nA + b * 256 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge (controller has a multi-edge?)'
    with open(sys.argv[3], 'w') as f:
        f.write(f"{2 * nA}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('controller m =', m, 'lift vertices', 2 * nA, 'edges', len(E))

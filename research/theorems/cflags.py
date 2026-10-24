"""Bipartite flag graph of the C_4 building W(7,2) (symplectic polar space of rank 4 over GF(2)).
Diagram C_4 = path 1-2-3-4 (types: t.i. subspaces of vector dimension 1..4), bipartition {1,3} | {2,4}.
Odd vertices: (point P1 < plane P3), even vertices: (line P2 < solid P4); adjacent iff P1 < P2 < P3 < P4.
(q+1)^2 = 9-regular.  Claim (Coxeter-element argument): diameter = Coxeter number h(C_4) = 8.
Order 2 * #chambers / 9 = 2 * [2]_2 [4]_2 [6]_2 [8]_2 / 9 = 160,650.
usage: python3 cflags.py OUT.edges
"""
import sys
from collections import deque


def B(x, y):  # symplectic form on GF(2)^8, pairs (0,1),(2,3),(4,5),(6,7)
    s = 0
    for k in range(0, 8, 2):
        s ^= (((x >> k) & 1) & ((y >> (k + 1)) & 1)) ^ (((x >> (k + 1)) & 1) & ((y >> k) & 1))
    return s


def span_add(S, z):
    return frozenset(S | {s ^ z for s in S} | {z})


def main():
    out = sys.argv[1]
    vecs = range(1, 256)
    perp = {x: [y for y in vecs if B(x, y) == 0] for x in vecs}
    def ext(S):   # t.i. subspaces containing S of one more dimension
        res = set()
        cand = set(vecs)
        for s in S:
            cand &= set(perp[s])
        for z in cand - S:
            res.add(span_add(S, z))
        return res
    pts = [frozenset([x]) for x in vecs]
    lines_of, planes_of, solids_of = {}, {}, {}
    for P in pts:
        lines_of[P] = ext(P)
    allL = set().union(*lines_of.values())
    for L in allL:
        planes_of[L] = ext(L)
    allP = set().union(*planes_of.values())
    for Pl in allP:
        solids_of[Pl] = ext(Pl)
    print("t.i. points", len(pts), "lines", len(allL), "planes", len(allP),
          "solids", len(set().union(*solids_of.values())))
    odd, even, edges = {}, {}, []
    for P in pts:
        for L in lines_of[P]:
            for Pl in planes_of[L]:
                for So in solids_of[Pl]:
                    o = odd.setdefault((P, Pl), len(odd))
                    e = even.setdefault((L, So), len(even))
                    edges.append((o, e))
    No = len(odd)
    nv = No + len(even)
    print("chambers", len(edges), "odd", No, "even", len(even), "vertices", nv)
    adj = [[] for _ in range(nv)]
    for o, e in edges:
        adj[o].append(No + e); adj[No + e].append(o)
    print("degrees", {len(a) for a in adj})
    for s in (0, No):
        dist = [-1] * nv; dist[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
        print("ecc from", "odd" if s == 0 else "even", "vertex:", max(dist), "unreached", dist.count(-1))
    with open(out, 'w') as f:
        f.write(f"{nv}\n")
        for o, e in edges: f.write(f"{o} {No + e}\n")


if __name__ == '__main__':
    main()

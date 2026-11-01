#!/usr/bin/env python3
"""Lean data for regular cyclic voltage lifts (lean/BipartiteDD/Haar/CycLift).

Usage: gen_cyclift.py EDGES.gz M D DEG NAME [LEANFILE]

Reads an edge list (first line n, then one edge per line) whose vertex v is (v // M, v % M), recovers the base graph
and the voltage of every base edge, and checks, before writing anything:
  1. every base pair carries whole fibres: each base edge (u, w, a) gives exactly the M lift edges (u, x) ~ (w, x + a);
  2. the lift rebuilt from the arc lists by the Lean formula (`CycLift.nbrs`: vertex w*M + x has the neighbours
     u*M + (x + b) % M for the arcs (u, b) out of w) has exactly the edges of the file;
  3. the graph is simple, DEG-regular and bipartite (the base 2-colouring `side` is proper);
  4. a BFS from every vertex (all pairs, no symmetry used) gives diameter exactly D;
  5. the per-base-vertex mask search of `CycLift.eccOK` (same rotation and OR steps) is full at radius D and
     not at radius D - 1.
Then it writes the Lean module with `outA`, `side` and the record theorem.
"""
import gzip
import hashlib
import sys
from collections import defaultdict, deque


def read_edges(path):
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as f:
        n = int(f.readline())
        edges = [tuple(map(int, l.split())) for l in f if l.strip()]
    return n, edges


def decode(n, edges, m):
    b = n // m
    assert b * m == n, 'n is not a multiple of M'
    cnt = defaultdict(int)
    for a, c in edges:
        u, x = divmod(a, m)
        w, y = divmod(c, m)
        cnt[(u, w, (y - x) % m)] += 1
        cnt[(w, u, (x - y) % m)] += 1
    for key, c in cnt.items():
        assert c == m, f'arc {key} carries {c} lift edges, not a whole fibre of {m}'
    outA = [sorted((w, a) for (u, w, a) in cnt if u == u0) for u0 in range(b)]
    return b, outA


def lean_nbrs(n, m, outA, v):
    w, x = divmod(v, m)
    return [(u * m + (x + beta) % m) % n for (u, beta) in outA[w]]


def edge_set(edges):
    return {(min(a, c), max(a, c)) for a, c in edges}


def bfs_ecc(adj, s):
    dist = [-1] * len(adj)
    dist[s] = 0
    q = deque([s])
    while q:
        v = q.popleft()
        for w in adj[v]:
            if dist[w] < 0:
                dist[w] = dist[v] + 1
                q.append(w)
    assert min(dist) >= 0, 'disconnected'
    return max(dist)


def rotR(m, beta, x):
    mask = (1 << m) - 1
    xm = x & mask
    return ((xm >> beta) | (xm << (m - beta))) & mask


def search_full(m, b, D, outA, u0):
    mask = (1 << m) - 1
    cur = [1 if w == u0 else 0 for w in range(b)]
    for _ in range(D):
        cur = [cur[w] | _or_rot(m, outA[w], cur) for w in range(b)]
    return all((x & mask) == mask for x in cur)


def _or_rot(m, arcs, cur):
    acc = 0
    for (u, beta) in arcs:
        acc |= rotR(m, beta, cur[u])
    return acc


def ecc_ok(m, b, D, outA):
    mask = (1 << m) - 1
    for u0 in range(b):
        cur = [1 if w == u0 else 0 for w in range(b)]
        for _ in range(D):
            nxt = []
            for w in range(b):
                acc = cur[w]
                for (u, beta) in outA[w]:
                    acc |= rotR(m, beta, cur[u])
                nxt.append(acc)
            cur = nxt
        if any((x & mask) != mask for x in cur):
            return False
    return True


def main():
    path, m, D, deg, name = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    leanfile = sys.argv[6] if len(sys.argv) > 6 else None
    raw = open(path, 'rb').read()
    sha = hashlib.sha256(gzip.decompress(raw) if path.endswith('.gz') else raw).hexdigest()
    n, edges = read_edges(path)
    b, outA = decode(n, edges, m)
    # 2. the Lean formula rebuilds the file
    E = edge_set(edges)
    assert len(E) == len(edges), 'repeated edge in the file'
    adj = [lean_nbrs(n, m, outA, v) for v in range(n)]
    F = {(min(v, w), max(v, w)) for v in range(n) for w in adj[v]}
    assert all(v != w for v in range(n) for w in adj[v]), 'loop'
    assert F == E, 'formula graph differs from the file'
    # 3. simple, regular, bipartite
    assert all(len(set(adj[v])) == len(adj[v]) == deg for v in range(n)), 'not simple and regular'
    assert all(v in adj[w] for v in range(n) for w in adj[v]), 'neighbour lists not symmetric'
    side = [None] * b
    side[0] = False
    q = deque([0])
    while q:
        w = q.popleft()
        for (u, _) in outA[w]:
            if side[u] is None:
                side[u] = not side[w]
                q.append(u)
            assert side[u] != side[w], 'base graph not bipartite'
    assert None not in side
    assert all(beta < m and u < b for w in range(b) for (u, beta) in outA[w])
    assert all((w, (m - beta) % m) in outA[u] for w in range(b) for (u, beta) in outA[w])
    # 4. all pairs
    diam = max(bfs_ecc(adj, s) for s in range(n))
    assert diam == D, f'diameter {diam}, not {D}'
    # 5. the Lean search
    assert ecc_ok(m, b, D, outA) and not ecc_ok(m, b, D - 1, outA)
    assert not search_full(m, b, D - 1, outA, 0), 'the search from base vertex 0 is full at D - 1'
    assert all(len(set(outA[w])) == len(outA[w]) == deg for w in range(b))
    print(f'{name}: n={n} b={b} m={m} edges={len(E)} degree={deg} bipartite diameter={diam} (all pairs) '
          f'eccOK at {D} and not at {D - 1}; sha256 {sha}')
    if not leanfile:
        return
    rows = ',\n'.join('  [' + ', '.join(f'({u}, {beta})' for (u, beta) in outA[w]) + ']' for w in range(b))
    sides = ', '.join('true' if s else 'false' for s in side)
    text = f'''import BipartiteDD.Haar.CycLift.Exact

/-! The ({deg},{D}) graph on {n} vertices: a regular `Z_{m}` voltage lift of a {b}-vertex cubic base graph.

Edge list: `{path[path.index('research/'):] if 'research/' in path else path}`
(uncompressed sha256 `{sha}`).
Base vertex `w` and fibre `x` give the vertex `w * {m} + x`. `outA{n}` lists, for each base vertex `w`, the arcs
`(u, β)`: `(w, x) ~ (u, x + β)`. Generated by `research/lean-haarD/gen_cyclift.py`, which checks that this formula
gives exactly the edges of the file, and that the graph has diameter {D} by a BFS from every vertex. -/

namespace BipartiteDD.CycLift

/-- The arcs out of each base vertex, with their voltages in `Z_{m}`. -/
def outA{n} : List (List (ℕ × ℕ)) := [
{rows}]

/-- A proper 2-colouring of the base graph. -/
def side{n} : List Bool := [{sides}]

/-- The lift. -/
def G{n} : SimpleGraph (Fin {n}) := liftGraph {n} {m} outA{n}

theorem G{n}_isBipartiteDegDiam : IsBipartiteDegDiam G{n} {deg} {D} :=
  isBipartiteDegDiam_of_checks (b := {b}) side{n} rfl (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Every vertex has exactly {deg} neighbours, and the diameter is exactly {D}. -/
theorem G{n}_exact : (∀ v, (G{n}.neighborSet v).ncard = {deg}) ∧ G{n}.ediam = {D} :=
  exact_of (b := {b}) side{n} [0] rfl (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) G{n}_isBipartiteDegDiam (by decide +kernel)

end BipartiteDD.CycLift

open BipartiteDD in
/-- A bipartite graph on {n} vertices, of degree at most {deg} and diameter at most {D}. -/
theorem nb_{deg}_{D}_{n} : ∃ G : SimpleGraph (Fin {n}), IsBipartiteDegDiam G {deg} {D} :=
  ⟨_, CycLift.G{n}_isBipartiteDegDiam⟩
'''
    with open(leanfile, 'w') as f:
        f.write(text)
    print('wrote', leanfile)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Lean data for Haar graphs of metacyclic groups, written as cyclic lifts (lean/BipartiteDD/Haar/CycLift).

Usage: gen_cychaar.py EDGES M K R D NAME [LEANFILE]

EDGES is the edge list of the Haar graph of G = Z_M x|_R Z_K, (a,j)(b,l) = (a + R^j b, j + l), in the numbering of
research/frontier/build_haar2.py: (g, A) -> idx(g) = a*K + j, (g, B) -> N + idx(g) (N = M*K), edges (g, A) ~ (s g, B).
(.gz or plain; first line n, then one edge per line.)

The Haar graph is a Z_M-lift of a base on 2K vertices: A_j = j, B_j = K + j. The vertex (a, j) of side A or B goes to
the fibre coordinate y = R^(-j) a mod M of A_j or B_j, i.e. the lift vertex (side*K + j)*M + y. An element s = (c, l)
of S gives the arc A_j -> B_(j+l) with voltage R^(-(j+l)) c, and the reverse arc with the negated voltage. Right
multiplication by (0, 1) becomes the base shift pi: A_j -> A_(j+1), B_j -> B_(j+1), with fibre multiplier mu = R^(-1).

Checks, before anything is written:
  1. S (read off the neighbours of vertex 0) rebuilds the file exactly under the group law above;
  2. the coordinate map sends the file's edges exactly onto the edges of the lift formula `CycLift.nbrs`;
  3. the lift is simple, 4-regular (|S|-regular) and bipartite; arcs are symmetric;
  4. (pi, mu) maps arcs to arcs (`autOK`), pi' and mu' = R invert them (`invOK`), the orbits of A_0, B_0 cover the base;
  5. the mask search of `CycLift.levM` from A_0 and B_0 is full at radius D and not at radius D - 1;
  6. a plain BFS in the Haar graph from (e, A) and (e, B) (the group acts transitively on each side) gives
     eccentricities with maximum exactly D and reaches every vertex.
"""
import gzip
import hashlib
import sys
from collections import deque


def read_edges(path):
    raw = open(path, 'rb').read()
    data = gzip.decompress(raw) if path.endswith('.gz') else raw
    sha = hashlib.sha256(data).hexdigest()
    lines = data.decode().split('\n')
    n = int(lines[0])
    edges = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
    return n, edges, sha


def rotR(m, beta, x):
    mask = (1 << m) - 1
    xm = x & mask
    return ((xm >> beta) | (xm << (m - beta))) & mask


def search_full(m, b, D, outA, u0):
    mask = (1 << m) - 1
    cur = [1 if w == u0 else 0 for w in range(b)]
    for _ in range(D):
        nxt = []
        for w in range(b):
            acc = cur[w]
            for (u, beta) in outA[w]:
                acc |= rotR(m, beta, cur[u])
            nxt.append(acc)
        cur = nxt
    return all((x & mask) == mask for x in cur)


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


def main():
    path, M, K, R, D, name = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), \
        sys.argv[6]
    leanfile = sys.argv[7] if len(sys.argv) > 7 else None
    n, edges, sha = read_edges(path)
    N = M * K
    assert n == 2 * N
    assert pow(R, K, M) == 1 % M, 'R^K != 1 mod M'
    Rinv = pow(R, -1, M)
    rp = [pow(R, j, M) for j in range(K)]
    rn = [pow(Rinv, j, M) for j in range(K)]

    def mul(g, h):
        return ((g[0] + rp[g[1]] * h[0]) % M, (g[1] + h[1]) % K)

    # 1. S from vertex 0, and the Haar graph it gives
    S = sorted({(v - N) for e in edges for v in e if (e[0] == 0 or e[1] == 0) and v != 0})
    S = [(i // K, i % K) for i in S]
    E = {(min(a, c), max(a, c)) for a, c in edges}
    assert len(E) == len(edges), 'repeated edge'
    H = set()
    for a in range(M):
        for j in range(K):
            for s in S:
                t = mul(s, (a, j))
                H.add((a * K + j, N + t[0] * K + t[1]))
    assert H == E, 'S does not rebuild the file'
    # the lift
    b = 2 * K
    outA = [[] for _ in range(b)]
    for (c, l) in S:
        for j in range(K):
            jl = (j + l) % K
            beta = rn[jl] * c % M
            outA[j].append((K + jl, beta))
            outA[K + jl].append((j, (M - beta) % M))
    outA = [sorted(x) for x in outA]

    def lift_nbrs(v):
        w, x = divmod(v, M)
        return [(u * M + (x + beta) % M) % n for (u, beta) in outA[w]]

    def phi_haar(v):
        side, idx = divmod(v, N)
        a, j = divmod(idx, K)
        return (side * K + j) * M + rn[j] * a % M

    # 2. the coordinate map sends the file onto the lift
    F = {(min(v, w), max(v, w)) for v in range(n) for w in lift_nbrs(v)}
    mapped = {(min(phi_haar(a), phi_haar(c)), max(phi_haar(a), phi_haar(c))) for a, c in E}
    assert len({phi_haar(v) for v in range(n)}) == n, 'coordinate map not a bijection'
    assert mapped == F, 'lift differs from the mapped file'
    # 3. simple, regular, bipartite, symmetric
    d = len(S)
    for v in range(n):
        nb = lift_nbrs(v)
        assert len(set(nb)) == len(nb) == d and v not in nb
    side = [w >= K for w in range(b)]
    assert all(side[w] != side[u] for w in range(b) for (u, _) in outA[w])
    assert all(u < b and beta < M for w in range(b) for (u, beta) in outA[w])
    assert all((w, (M - beta) % M) in outA[u] for w in range(b) for (u, beta) in outA[w])
    # 4. automorphism and orbits
    pi = lambda w: (w + 1) % K if w < K else K + (w - K + 1) % K
    pinv = lambda w: (w + K - 1) % K if w < K else K + (w - K + K - 1) % K
    mu, mup = Rinv, R % M
    assert all(pi(w) < b and pinv(w) < b and pi(pinv(w)) == w and pinv(pi(w)) == w for w in range(b))
    assert mu * mup % M == 1 % M
    assert all((pi(u), mu * beta % M) in outA[pi(w)] for w in range(b) for (u, beta) in outA[w])
    orb = set()
    for u0 in (0, K):
        u = u0
        for _ in range(K):
            orb.add(u)
            u = pi(u)
    assert orb == set(range(b))
    # 5. the Lean search
    assert search_full(M, b, D, outA, 0) and search_full(M, b, D, outA, K)
    assert not search_full(M, b, D - 1, outA, 0), 'the search from A_0 is full at D - 1'
    assert all(len(set(outA[w])) == len(outA[w]) == len(S) for w in range(b))
    # 6. plain BFS in the Haar graph
    adj = [[] for _ in range(n)]
    for a, c in E:
        adj[a].append(c)
        adj[c].append(a)
    eA, eB = bfs_ecc(adj, 0), bfs_ecc(adj, N)
    assert max(eA, eB) == D, (eA, eB)
    print(f'{name}: n={n} meta {M} {K} {R} S={S} edges={len(E)} degree={d} bipartite; ecc(e,A)={eA} ecc(e,B)={eB}; '
          f'lift base {b} x Z_{M}; searches full at {D}, not at {D - 1}; sha256 {sha}')
    if not leanfile:
        return
    rows = ',\n'.join('  [' + ', '.join(f'({u}, {beta})' for (u, beta) in outA[w]) + ']' for w in range(b))
    rel = path[path.index('research/'):] if 'research/' in path else path
    Sstr = ', '.join(f'({c}, {l})' for (c, l) in S)
    text = f'''import BipartiteDD.Haar.CycLift.Exact

/-! The ({d},{D}) graph on {n} vertices: the Haar graph of `Z_{M} ⋊_{R} Z_{K}` with
`S = {{{Sstr}}}` (elements `(a, j)`, product `(a, j) (b, l) = (a + {R}^j b, j + l)`), written as a `Z_{M}`-lift of
a base graph on {b} vertices.

Edge list: `{rel}` (uncompressed sha256 `{sha}`).
Base vertices `A_j = j` and `B_j = {K} + j`. The group element `(a, j)` on side A (or B) is the lift vertex
`w * {M} + y` with `w = A_j` (or `B_j`) and `y = {R}^(-j) a mod {M}`. The element `(c, l)` of `S` gives the arc
`A_j → B_(j+l)` with voltage `{R}^(-(j+l)) c`. Right multiplication by `(0, 1)` is the automorphism
`(w, y) ↦ (π w, {mu} y)` (`{mu} = {R}⁻¹ mod {M}`), so the searches from `A_0` and `B_0` cover every vertex.
Generated by `research/lean-haarD/gen_cychaar.py`, which checks that the coordinate map sends the edges of the file
exactly onto the edges of this lift, and that the Haar graph has diameter {D} by BFS. -/

namespace BipartiteDD.CycLift

/-- The arcs out of each base vertex, with their voltages in `Z_{M}`. -/
def outA{n} : List (List (ℕ × ℕ)) := [
{rows}]

/-- Side A is `false`, side B is `true`. -/
def side{n} : List Bool := (List.range {b}).map fun w => decide ({K} ≤ w)

/-- The coset shift `A_j ↦ A_(j+1)`, `B_j ↦ B_(j+1)`. -/
def pi{n} (w : ℕ) : ℕ := if w < {K} then (w + 1) % {K} else {K} + (w - {K} + 1) % {K}

/-- Its inverse. -/
def piInv{n} (w : ℕ) : ℕ := if w < {K} then (w + {K - 1}) % {K} else {K} + (w - {K} + {K - 1}) % {K}

/-- The lift. -/
def G{n} : SimpleGraph (Fin {n}) := liftGraph {n} {M} outA{n}

theorem G{n}_isBipartiteDegDiam : IsBipartiteDegDiam G{n} {d} {D} :=
  isBipartiteDegDiam_of_srcs (b := {b}) (π := pi{n}) (π' := piInv{n}) (μ := {mu}) (μ' := {mup}) (K := {K})
    side{n} [0, {K}] rfl (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Every vertex has exactly {d} neighbours, and the diameter is exactly {D}. -/
theorem G{n}_exact : (∀ v, (G{n}.neighborSet v).ncard = {d}) ∧ G{n}.ediam = {D} :=
  exact_of (b := {b}) side{n} [0] rfl (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) G{n}_isBipartiteDegDiam (by decide +kernel)

end BipartiteDD.CycLift

open BipartiteDD in
/-- A bipartite graph on {n} vertices, of degree at most {d} and diameter at most {D}. -/
theorem nb_{d}_{D}_{n} : ∃ G : SimpleGraph (Fin {n}), IsBipartiteDegDiam G {d} {D} :=
  ⟨_, CycLift.G{n}_isBipartiteDegDiam⟩
'''
    with open(leanfile, 'w') as f:
        f.write(text)
    print('wrote', leanfile)


if __name__ == '__main__':
    main()

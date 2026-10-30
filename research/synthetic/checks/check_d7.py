r"""Checks for Section 4 of SYNTHETIC.tex (diameter 7: copies of a hexagon joined by matchings,
freed sets and hubs), on H(2) and H(3) built as in check_d6.py.

  1. Theorem A: 2r+1 copies of H(q) joined by arbitrary bijections points -> lines (r = 1, 2; q = 2):
     (q+1+r)-regular, diameter 7.
  2. Theorem B (friendly transition, identity, q = 3): freeing the point set of a spread (a segment
     set of the largest size) leaves the transition repaired; freeing a set with a turning triple
     does not (Remark 4.2 of D7_HEXAGON.md).  Also: a set of points of a spread is a segment set.
  3. Theorem C (q = 3): a bijection points -> lines that is a local duality at every point of a
     pairwise opposite set R onto a pairwise opposite set of lines (built as in Proposition 5.2):
     the transition freed at R is repaired.
  4. Assembly (q = 3, r = 1): three copies, the same local duality on every transition, R freed on
     every transition, |R| line-hubs and |R| point-hubs joined by a 6-cycle: max degree q+2,
     diameter 7, 6N + 2|R| elements.

Run: python3 check_d7.py
"""
import itertools
import random
import sys
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from check_d6 import hexagon  # noqa: E402

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


class Graph:
    def __init__(self):
        self.adj = {}

    def add(self, u, v):
        self.adj.setdefault(u, set()).add(v)
        self.adj.setdefault(v, set()).add(u)

    def bfs(self, s, limit=None):
        dist = {s: 0}
        dq = deque([s])
        while dq:
            u = dq.popleft()
            if limit is not None and dist[u] >= limit:
                continue
            for w in self.adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    dq.append(w)
        return dist

    def diameter(self):
        names = list(self.adj)
        idx = {v: i for i, v in enumerate(names)}
        bits = [0] * len(names)
        for v, ws in self.adj.items():
            b = 0
            for w in ws:
                b |= 1 << idx[w]
            bits[idx[v]] = b
        n = len(names)
        full = (1 << n) - 1
        best = 0
        for v in range(n):
            ball = fr = 1 << v
            r = 0
            while ball != full:
                nxt = 0
                b = fr
                while b:
                    low = b & -b
                    nxt |= bits[low.bit_length() - 1]
                    b ^= low
                fr = nxt & ~ball
                if not fr:
                    return None
                ball |= nxt
                r += 1
            best = max(best, r)
        return best

    def maxdeg(self):
        return max(len(w) for w in self.adj.values())


def incidence_graph(H):
    G = Graph()
    for p, L in H.flags:
        G.add(p, L)
    return G


def level_copy(G, H, j, Gbig):
    for p, L in H.flags:
        Gbig.add((p, j), (L, j))


def all_dist(H):
    I = incidence_graph(H)
    return {x: I.bfs(x) for x in I.adj}


def theorem_A(q, r, rng):
    H, _, _ = hexagon(q)
    P, L = list(H.points), list(H.lines)
    n_lev = 2 * r + 1
    G = Graph()
    for j in range(n_lev):
        level_copy(None, H, j, G)
    for j in range(n_lev):
        for k in range(1, r + 1):
            Ls = L[:]
            rng.shuffle(Ls)
            for p, l in zip(P, Ls):
                G.add((p, j), (l, (j + k) % n_lev))
    check(len(G.adj) == n_lev * 2 * len(P), f'Theorem A q={q} r={r}: (2r+1)2N vertices')
    check({len(w) for w in G.adj.values()} == {q + 1 + r}, f'Theorem A q={q} r={r}: regular of degree q+1+r')
    check(G.diameter() == 7, f'Theorem A q={q} r={r}: diameter 7')


def two_level_repaired(H, M, freed):
    """Level 0 a copy of H, level 1 a copy of H (or of its dual: then M maps points to points, which are
    the 'lines' of the dual copy).  M: dict from points of level 0 to elements of level 1.  Returns True
    if every vertex of level 0 is within distance 7 of every vertex of level 1 after deleting the
    matching edges at the freed points."""
    G = Graph()
    for j in (0, 1):
        level_copy(None, H, j, G)
    for p, y in M.items():
        if p not in freed:
            G.add((p, 0), (y, 1))
    lvl1 = [x for x in G.adj if x[1] == 1]
    for s in [x for x in G.adj if x[1] == 0]:
        d = G.bfs(s, limit=7)
        if any(x not in d for x in lvl1):
            return False
    return True


def is_segment_set(H, F):
    F = set(F)
    for p in F:
        lines_with = [L for L in H.lines_on[p] if len((H.pts_on[L] & F) - {p}) > 0]
        if len(lines_with) > 1:
            return False
    return True


def theorem_B(q, rng):
    H, names, lines = hexagon(q)
    # a spread: the Hermitian spread X0 + c X4 = 0 (q = 3, c = 1)
    Spts = {p for p in H.points if (p[0] + p[4]) % q == 0}
    S = [L for L in H.lines if H.pts_on[L] <= Spts]
    check(len(S) == q ** 3 + 1, 'B: spread')
    F = set().union(*(H.pts_on[L] for L in S))
    check(is_segment_set(H, F) and len(F) == (q + 1) * (q ** 3 + 1), 'B: the point set of a spread is a segment set of size (q+1)(q^3+1)')
    M = {p: p for p in H.points}   # friendly transition H -> D, identity
    check(two_level_repaired(H, M, F), 'B: friendly identity transition freed at a spread point set is repaired')
    # a turning triple p - m - p' - m' - p''
    p1 = H.points[0]
    m, m2 = sorted(H.lines_on[p1], key=str)[:2]
    p0 = next(x for x in H.pts_on[m] if x != p1)
    p2 = next(x for x in H.pts_on[m2] if x != p1)
    check(not is_segment_set(H, {p0, p1, p2}), 'B: a turning triple is not a segment set')
    check(not two_level_repaired(H, M, {p0, p1, p2}), 'B: freeing a turning triple breaks the transition (Remark 4.2)')
    # a random non-collinear set is a segment set and is repaired
    R = []
    for p in rng.sample(H.points, len(H.points)):
        if all(not (H.lines_on[p] & H.lines_on[x]) for x in R):
            R.append(p)
    check(is_segment_set(H, R), 'B: a non-collinear set is a segment set')
    check(two_level_repaired(H, M, set(R)), f'B: friendly transition freed at a maximal non-collinear set ({len(R)} points) is repaired')
    return H, S


def pairwise_opposite(H, dist, items, rng, size):
    out = []
    for x in rng.sample(items, len(items)):
        if all(dist[x][y] == 6 for y in out):
            out.append(x)
            if len(out) == size:
                break
    return out


def local_duality(H, dist, R, Rstar, rng):
    """Proposition 5.2 with no pairs at distance 4 (R, R* pairwise opposite): M(x) = f(x) on R; for
    each x in R a bijection from the points collinear with x onto the lines concurrent with f(x);
    any bijection on the rest."""
    M = {}
    for x, y in zip(R, Rstar):
        M[x] = y
        cp = sorted({z for L in H.lines_on[x] for z in H.pts_on[L]} - {x}, key=str)
        cl = sorted({N for z in H.pts_on[y] for N in H.lines_on[z]} - {y}, key=str)
        assert len(cp) == len(cl) == q_of(H) * (q_of(H) + 1)
        rng.shuffle(cl)
        for a, b in zip(cp, cl):
            assert a not in M
            M[a] = b
    used = set(M.values())
    restP = [p for p in H.points if p not in M]
    restL = [L for L in H.lines if L not in used]
    rng.shuffle(restL)
    for a, b in zip(restP, restL):
        M[a] = b
    assert len(M) == len(H.points) and len(set(M.values())) == len(H.lines)
    return M


def q_of(H):
    return len(next(iter(H.pts_on.values()))) - 1


def theorem_C_and_assembly(q, rng, K):
    H, names, lines = hexagon(q)
    dist = all_dist(H)
    R = pairwise_opposite(H, dist, H.points, rng, K)
    Rstar = pairwise_opposite(H, dist, H.lines, rng, K)
    check(len(R) == len(Rstar) == K, f'C: pairwise opposite sets of size {K}')
    M = local_duality(H, dist, R, Rstar, rng)
    # local duality at x: M maps the points collinear with x onto the lines concurrent with M(x)
    for x in R:
        cp = {z for L in H.lines_on[x] for z in H.pts_on[L]} - {x}
        cl = {N for z in H.pts_on[M[x]] for N in H.lines_on[z]} - {M[x]}
        check({M[z] for z in cp} == cl, 'C: M is a local duality at every point of R')
    check(two_level_repaired(H, M, set(R)), 'C: transition freed at R is repaired')
    # a bijection that is NOT a local duality at R: shuffle; freeing R typically breaks it
    # assembly: three copies, M on each transition, R freed on each, hubs joined by a cycle
    N = len(H.points)
    G = Graph()
    for j in range(3):
        level_copy(None, H, j, G)
    for j in range(3):
        for p, y in M.items():
            if p not in R:
                G.add((p, j), (y, (j + 1) % 3))
    hB = [('hubB', i) for i in range(K)]
    hA = [('hubA', i) for i in range(K)]
    for i, x in enumerate(R):
        for j in range(3):
            G.add(hB[i], (x, j))            # line-hub: one freed point (slot) in every level
            G.add(hA[i], (M[x], j))         # point-hub: one freed line in every level
    for i in range(K):                      # hub graph: a 2K-cycle (degree 2 <= q - r)
        G.add(hB[i], hA[i])
        G.add(hA[i], hB[(i + 1) % K])
    check(G.maxdeg() == q + 2, f'assembly q={q}: maximum degree q+2')
    check(len(G.adj) == 6 * N + 2 * K, f'assembly q={q}: 6N + 2|R| elements')
    d = G.diameter()
    check(d == 7, f'assembly q={q}: diameter 7 (got {d})')
    return d


def main():
    rng = random.Random(11)
    theorem_A(2, 1, rng)
    theorem_A(2, 2, rng)
    print('Theorem A on H(2), r = 1, 2, random matchings: checked')
    theorem_B(3, rng)
    print('Theorem B on H(3) (friendly identity transition; spread points, non-collinear set; turning triple): checked')
    theorem_C_and_assembly(3, rng, 3)
    print('Theorem C and the assembly with hubs on H(3), |R| = 3: checked')
    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')
    return not FAIL


if __name__ == '__main__':
    sys.exit(0 if main() else 1)

"""The table's D = 7 construction, rebuilt: three copies of the incidence graph of H(q) plus one doubled perfect
matching, i.e. the Z_3-lift of (Gamma + M') with voltage 1 on the extra copy of M and 0 elsewhere.

Vertices (v, c), v in V(Gamma) (points 0..P-1, lines P..2P-1), c in Z_3; index c*2P + v.
Edges: (p, c) ~ (L, c) for p on L (all c); cross edges (p, c) ~ (M(p), c+1) for every point p, M a perfect matching
of Gamma (p on M(p)). Max degree q + 2, 6P vertices, diameter 7 for ANY perfect matching M (proof in the report:
first step along one's own cross edge covers the next copy, last step into a target along its cross edge covers
the previous one).

usage: python3 threecopy.py q OUT.edges        (writes 'n' then one 'a b' per line, the format of apsp.c)
"""
import sys
from hexagon import build


def perfect_matching(P, lines_of_pt, pts_of_line):
    """Hopcroft-Karp style augmenting paths (iterative DFS) on the regular bipartite incidence graph"""
    match_p = [-1] * P   # point -> line
    match_l = [-1] * P   # line -> point
    # greedy start
    for p in range(P):
        for l in lines_of_pt[p]:
            if match_l[l] < 0:
                match_p[p], match_l[l] = l, p
                break
    for p0 in range(P):
        if match_p[p0] >= 0:
            continue
        # BFS for an augmenting path from p0
        prev = {}
        frontier = [p0]
        seen_l = set()
        found = None
        while frontier and found is None:
            nxt = []
            for p in frontier:
                for l in lines_of_pt[p]:
                    if l in seen_l:
                        continue
                    seen_l.add(l)
                    prev[l] = p
                    if match_l[l] < 0:
                        found = l
                        break
                    nxt.append(match_l[l])
                if found is not None:
                    break
            frontier = nxt
        assert found is not None
        l = found
        while True:
            p = prev[l]
            nl = match_p[p]
            match_p[p], match_l[l] = l, p
            if p == p0:
                break
            l = nl
    assert all(m >= 0 for m in match_p)
    return match_p


def three_copy_edges(P, pts_of_line, lines_of_pt, M):
    n = 6 * P
    E = []
    for c in range(3):
        base = c * 2 * P
        for l, ln in enumerate(pts_of_line):
            for p in ln:
                E.append((base + p, base + P + l))
        nb = ((c + 1) % 3) * 2 * P
        for p in range(P):
            E.append((base + p, nb + P + M[p]))
    return n, E


if __name__ == '__main__':
    q = int(sys.argv[1])
    P, pl, lp = build(q)
    M = perfect_matching(P, lp, pl)
    n, E = three_copy_edges(P, pl, lp, M)
    with open(sys.argv[2], 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % e for e in E))
    print('wrote %s: n=%d edges=%d (3 copies of H(%d), max degree %d)' % (sys.argv[2], n, len(E), q, q + 2))

"""Exact-cover search (sizes 21): pairwise disjoint lines covering all 63 points (a spread), and pairwise non-collinear
points meeting every line once (a 21-element coclique). Usage: python3 h2_exact.py"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/polylev/r1/c13')
from h2_build import LP, PL, N, ADJ_LINES, ADJ_POINTS


def exact_cover(sets, universe, limit=10**6):
    """choose sets (indices) pairwise disjoint covering the universe; returns one solution or None"""
    cover_of = {u: [i for i, s in enumerate(sets) if u in s] for u in universe}
    chosen, used = [], set()
    nodes = [0]

    def rec(unc):
        nodes[0] += 1
        if nodes[0] > limit:
            raise RuntimeError('limit')
        if not unc:
            return True
        u = min(unc, key=lambda x: sum(1 for i in cover_of[x] if not (set(sets[i]) & used)))
        for i in cover_of[u]:
            s = set(sets[i])
            if s & used:
                continue
            chosen.append(i)
            used.update(s)
            if rec(unc - s):
                return True
            used.difference_update(s)
            chosen.pop()
        return False

    ok = rec(set(universe))
    return sorted(chosen) if ok else None, nodes[0]


if __name__ == '__main__':
    spread, n1 = exact_cover([set(x) for x in LP], range(N))
    print('spread (21 pairwise disjoint lines covering the points):', spread, 'nodes', n1)
    # points: choose points whose line sets partition the lines
    coind, n2 = exact_cover([set(x) for x in PL], range(N))
    print('21 pairwise non-collinear points covering the lines once:', coind, 'nodes', n2)
    if spread:
        assert all(not (set(LP[a]) & set(LP[b])) for a in spread for b in spread if a < b)
    if coind:
        assert all(not (set(PL[a]) & set(PL[b])) for a in coind for b in coind if a < b)

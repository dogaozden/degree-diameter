#!/usr/bin/env python3
"""Can the A side of an F_3 route chart be perfect?  A-side patterns are all nonsingular iff the four tripods
T_j = A_j^-1 (tripod at b_j: the point b_j and the lines <b_j, b_i>, i != j) are pairwise disjoint, i.e. partition the
40 points of PG(3,3) (4 x 10 = 40).  With the gauge A_0 = I, T_0 is the tripod at b_0 itself.
This script fixes the configuration of b_0..b_3 (independent, or a plane frame), and counts the ways to partition
the complement of T_0 into three tripods of the same kind (non-coplanar for independent b's, coplanar for a plane frame).
usage: python3 tripods.py"""
import itertools

PTS = []
for v in itertools.product(range(3), repeat=4):
    if any(v):
        f = next(x for x in v if x)
        if f == 1:
            PTS.append(v)
IDX = {p: i for i, p in enumerate(PTS)}
assert len(PTS) == 40

def norm(v):
    v = tuple(x % 3 for x in v)
    f = next(x for x in v if x)
    return tuple((x * f) % 3 for x in v)          # f^-1 = f in F_3

def line(p, q):
    return frozenset(IDX[norm(tuple(a * x + b * y for x, y in zip(p, q)))]
                     for a in range(3) for b in range(3) if (a, b) != (0, 0))

LINES = sorted({line(p, q) for p in PTS for q in PTS if p != q}, key=sorted)
assert len(LINES) == 130

def coplanar(l1, l2, l3):
    pts = set(l1) | set(l2) | set(l3)
    # three concurrent lines are coplanar iff their union has 10 points AND lies in a plane: check rank
    M = [PTS[i] for i in pts]
    return rank(M) == 3

def rank(vecs):
    rows = [list(v) for v in vecs]; r = 0
    for col in range(4):
        piv = next((i for i in range(r, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        if rows[r][col] == 2:
            rows[r] = [(2 * x) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def tripods(kind):
    """all tripods (apex, 3 lines) as point bitmasks; kind = 'skew' (non-coplanar) or 'flat' (coplanar)"""
    out = {}
    for p in range(40):
        through = [l for l in LINES if p in l]
        for l1, l2, l3 in itertools.combinations(through, 3):
            c = coplanar(l1, l2, l3)
            if (kind == 'flat') == c:
                mask = 0
                for i in l1 | l2 | l3:
                    mask |= 1 << i
                out.setdefault(mask, []).append((p, (l1, l2, l3)))
    return out

def count_partitions(T0mask, tri):
    full = (1 << 40) - 1
    rest = full & ~T0mask
    cand = [m for m in tri if m & T0mask == 0]
    sols = []
    low = lambda x: (x & -x).bit_length() - 1
    def rec(rem, chosen):
        if rem == 0:
            sols.append(tuple(chosen)); return
        i = low(rem)
        for m in cand:
            if (m >> i) & 1 and m & ~rem == 0:
                rec(rem & ~m, chosen + [m])
    rec(rest, [])
    return sols

if __name__ == '__main__':
    e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    for name, bs, kind in [('independent b', e, 'skew'),
                           ('plane frame b', [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 1, 1, 0)], 'flat')]:
        tri = tripods(kind)
        T0 = line(bs[0], bs[1]) | line(bs[0], bs[2]) | line(bs[0], bs[3])
        m0 = 0
        for i in T0:
            m0 |= 1 << i
        sols = count_partitions(m0, tri)
        print(f"{name}: |T_0| = {len(T0)}, {len(tri)} {kind} tripod point-sets, partitions of the complement: {len(sols)}")

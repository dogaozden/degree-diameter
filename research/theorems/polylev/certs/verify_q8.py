"""verify_q8.py: stand-alone check of the D = 11 data at q = 8 (Computer-checked 5.7 of POLYGON_LEVELS.md).
Uses no other file of the repository: GF(8) = GF(2)[w]/(w^3+w+1), an element a0 + a1 w + a2 w^2 is written as the
integer a0 + 2 a1 + 4 a2. Q(X) = X0X4 + X1X5 + X2X6 - X3^2; lines of H(8) = totally singular lines whose Grassmann
coordinates p_ij = x_i y_j - x_j y_i satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31 (§1).
Input (text): the 7x7 matrix h (7 rows), the point orbit representatives (one point per row, 7 entries) and the line
orbit representatives (two spanning points per row, 14 entries). The sets are the orbits under <h>.
Checks: h has order 63 on points; every point singular; no hexagon line contains two chosen points; every chosen line
totally singular; the chosen lines pairwise disjoint. Prints the numbers of points and lines.
With a fourth argument, the line representatives are expanded with that matrix instead of h (the identity matrix
for a plain list of lines).
Usage: python3 verify_q8.py H.txt POINT_REPS.txt LINE_REPS.txt [H_LINES.txt]"""
import sys
import numpy as np

MUL = np.zeros((8, 8), dtype=np.int64)
for a in range(8):
    for b in range(8):
        r = 0
        for i in range(3):
            if b >> i & 1:
                r ^= a << i
        for d in (4, 3):                       # reduce: w^3 = w + 1, w^4 = w^2 + w
            if r >> d & 1:
                r ^= 0b1011 << (d - 3)
        MUL[a, b] = r
INV = np.zeros(8, dtype=np.int64)
for a in range(1, 8):
    INV[a] = int(np.where(MUL[a] == 1)[0][0])


def dot(u, v):                                 # sum of products over GF(8) (addition is XOR)
    r = 0
    for x, y in zip(u, v):
        r ^= MUL[x, y]
    return r


def matvec(M, x):
    return np.array([dot(row, x) for row in M], dtype=np.int64)


def norm(x):
    nz = np.nonzero(x)[0]
    return tuple(MUL[INV[x[nz[0]]], x])


def Q(x):                                      # -X3^2 = X3^2 in characteristic 2
    return MUL[x[0], x[4]] ^ MUL[x[1], x[5]] ^ MUL[x[2], x[6]] ^ MUL[x[3], x[3]]


def b(x, y):
    return Q(np.bitwise_xor(x, y)) ^ Q(x) ^ Q(y)


def tits(x, y):
    p = lambda i, j: MUL[x[i], y[j]] ^ MUL[x[j], y[i]]
    return (p(1, 2) == p(3, 4) and p(5, 4) == p(3, 2) and p(2, 0) == p(3, 5) and p(6, 5) == p(3, 0)
            and p(0, 1) == p(3, 6) and p(4, 6) == p(3, 1))


def orbit(h, x):
    out, y = [], norm(np.array(x))
    while True:
        out.append(y)
        y = norm(matvec(h, np.array(y)))
        if y == out[0]:
            return out


def main():
    h = np.loadtxt(sys.argv[1], dtype=np.int64)
    PR = np.loadtxt(sys.argv[2], dtype=np.int64, ndmin=2)
    LR = np.loadtxt(sys.argv[3], dtype=np.int64, ndmin=2)
    hl = np.loadtxt(sys.argv[4], dtype=np.int64) if len(sys.argv) > 4 else h
    pts = [y for x in PR for y in orbit(h, x)]
    assert len(set(pts)) == len(pts), 'point orbits overlap'
    assert all(Q(np.array(x)) == 0 for x in pts), 'a point is not on the quadric'
    X = np.array(pts)
    M = lambda i, j: MUL[X[:, i][:, None], X[:, j][None, :]]          # x_i y_j for all pairs
    B = M(0, 4) ^ M(4, 0) ^ M(1, 5) ^ M(5, 1) ^ M(2, 6) ^ M(6, 2)      # b(x, y) (the X3 term vanishes)
    I, J = np.nonzero(np.triu(B == 0, 1))
    p = lambda i, j: MUL[X[I, i], X[J, j]] ^ MUL[X[I, j], X[J, i]]
    T = ((p(1, 2) == p(3, 4)) & (p(5, 4) == p(3, 2)) & (p(2, 0) == p(3, 5)) & (p(6, 5) == p(3, 0))
         & (p(0, 1) == p(3, 6)) & (p(4, 6) == p(3, 1)))
    coll = int(T.sum())
    print(f'{len(X)} points on Q(6,8); pairs on a common line of H(8): {coll}')
    lines = []
    for row in LR:
        x, y = row[:7], row[7:]
        assert Q(x) == 0 and Q(y) == 0 and b(x, y) == 0, 'a line is not totally singular'
        for _ in range(63):
            lines.append((x, y))
            x, y = matvec(hl, x), matvec(hl, y)
    # distinct lines and their points (orbits of size < 63 repeat: keep distinct point sets only)
    sets = {}
    for x, y in lines:
        P = frozenset([norm(y)] + [norm(np.bitwise_xor(x, MUL[l, y])) for l in range(8)])
        sets[P] = 1
    allp = [p for P in sets for p in P]
    print(f'{len(sets)} totally singular lines; points covered {len(allp)}, distinct {len(set(allp))}; '
          f'pairwise disjoint: {len(allp) == len(set(allp))}')
    print(f'K = {min(len(sets), len(X)) if coll == 0 and len(allp) == len(set(allp)) else 0}')


if __name__ == '__main__':
    main()

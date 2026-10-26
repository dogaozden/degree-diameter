"""gen3.py: pencil-dual lift at q with a choice of projective coordinate per matching (own card c3, round 2).

Each coordinate is a map u -> (X(u) : Y(u)) in PG(1,q), X, Y forms in u built from the polar form b:
  lin : X = b(a,u),        Y = b(a2,u)              (linear pencil coordinate, as in pencil_dual.py)
  qA  : X = b(a,u)b(a2,u), Y = b(a3,u)^2            (degree-2 coordinate)
  qB  : X = b(a,u)^2,      Y = b(a2,u)b(a3,u)
  qC  : X = b(a,u)^2,      Y = b(a2,u)^2            (square of lin)
  qD  : X = b(a,u)b(a2,u), Y = b(a,u)^2 + b(a3,u)^2
Value of (X:Y) is index X/Y in 0..q-1, or q for infinity; (0:0) gets a random value (axis).
Voltages: beta1 = 1 + F1(p), beta2 = q+2 + F2(p) mod m (same blocks as pencil_dual.py).
Usage: python3 gen3.py q phifile m seed OUT F1 F2
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load


def gf_tables(q):
    polys = {4: ([1, 1], 2), 8: ([1, 1, 0], 3), 9: ([1, 0], 2), 16: ([1, 1, 0, 0], 4), 25: ([2, 0], 2),
             27: ([1, 2, 0], 3), 32: ([1, 0, 1, 0, 0], 5)}
    p = next(d for d in range(2, q + 1) if q % d == 0)
    cfs, e = polys.get(q, ([0], 1))
    def dig(x):
        out = []
        for _ in range(e):
            out.append(x % p); x //= p
        return out
    def enc(v):
        s, pw = 0, 1
        for d in v:
            s += d * pw; pw *= p
        return s
    ADD = [[enc([(u + v) % p for u, v in zip(dig(x), dig(y))]) for y in range(q)] for x in range(q)]
    MUL = [[0] * q for _ in range(q)]
    for x in range(q):
        for y in range(q):
            a, b = dig(x), dig(y)
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if not f:
                    continue
                r[k] = 0
                for i in range(e):
                    r[k - e + i] = (r[k - e + i] - f * cfs[i]) % p
            MUL[x][y] = enc(r[:e])
    NEG = [next(y for y in range(q) if ADD[x][y] == 0) for x in range(q)]
    INV = [0] + [next(y for y in range(q) if MUL[x][y] == 1) for x in range(1, q)]
    return ADD, MUL, NEG, INV


def main():
    q, phif, m, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    F1spec, F2spec = sys.argv[6], sys.argv[7]
    N, LP, PL, coord = load(q)
    phi = np.fromfile(phif, dtype=np.int32).astype(np.int64)
    assert phi.shape[0] == 2 * N
    C = coord.astype(np.int64)
    rng = np.random.default_rng(seed)
    ADD, MUL, NEG, INV = gf_tables(q)
    a, a2, a3 = (rng.integers(0, q, 7) for _ in range(3))
    PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
    two = ADD[1][1]

    def bform(x, y):
        acc = 0
        for i, j in PAIRS:
            acc = ADD[acc][MUL[x[i]][y[j]]]
        return ADD[acc][NEG[MUL[two][MUL[x[3]][y[3]]]]]

    def sq(x):
        return MUL[x][x]

    def coordfun(spec):
        # returns array of values in 0..q (q = infinity, -1 = axis)
        vals = np.empty(N, dtype=np.int64)
        nspec = 0
        for p in range(N):
            u = C[p]
            ba, ba2, ba3 = bform(u, a), bform(u, a2), bform(u, a3)
            if spec == 'lin':
                X, Y = ba, ba2
            elif spec == 'qA':
                X, Y = MUL[ba][ba2], sq(ba3)
            elif spec == 'qB':
                X, Y = sq(ba), MUL[ba2][ba3]
            elif spec == 'qC':
                X, Y = sq(ba), sq(ba2)
            elif spec == 'qD':
                X, Y = MUL[ba][ba2], ADD[sq(ba)][sq(ba3)]
            else:
                raise SystemExit('unknown spec ' + spec)
            if Y != 0:
                vals[p] = MUL[X][INV[Y]]
            elif X != 0:
                vals[p] = q
            else:
                vals[p] = -1
                nspec += 1
        spec_rand = rng.integers(0, q + 1, N)
        vals = np.where(vals < 0, spec_rand, vals)
        return vals, nspec

    F1, n1 = coordfun(F1spec)
    F2, n2 = coordfun(F2spec)
    b1 = (1 + F1) % m
    b2 = (q + 2 + F2) % m
    with open(out, 'w') as f:
        f.write(f'Z {m}\n{2 * N}\n')
        f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
        for l in range(N):
            for p in LP[l]:
                f.write(f'{p} {N + l} 0\n')
        for p in range(N):
            f.write(f'{p} {phi[p]} {b1[p]}\n')
            f.write(f'{p} {phi[p]} {b2[p]}\n')
    print(f'q {q} m {m} F1 {F1spec} F2 {F2spec} axis {n1} {n2}', file=sys.stderr)


if __name__ == '__main__':
    main()

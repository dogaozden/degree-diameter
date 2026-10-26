"""pencil_dual.py: Z_m lift of I(H(q)) + a duality used twice, with "pencil coordinate" voltages (own-d8-compound).

Base: points 0..N-1, lines N..2N-1 of H(q); GF(q) elements encoded as in hexgen2.c (a0 + a1 p + ..., fixed
irreducible polynomial), so prime powers work too.
Matchings: for every point p two parallel edges p -- delta(p) with voltages f1(c(p)) and f2(c(p)), where delta is a
duality of H(q) (file from research/d10D7/dual/dualfind.c: 2N int32, delta(p) = phi[p] in N..2N-1, delta(l) = phi[N+l])
and c(p) = [b(a,p) : b(a',p)] in PG(1,q) for two fixed vectors a, a' (b = polar form of the quadric).
Hexagon voltages 0.  Blocks: f1 = 1 + c, f2 = q+2 + c, so {0} u A1 u A2 u -A1 u -A2 = Z_m for m = 4q+5.
Points with b(a,p) = b(a',p) = 0 get c = SPECIAL (argument).
Usage: python3 pencil_dual.py q phifile m seed OUT [mode]   mode: 'same' (delta twice, default) or 'inv' (delta, delta^-1)
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load


def gf_tables(q):
    """GF(q) tables in the encoding of hexgen2.c."""
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

q, phif, m, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
mode = sys.argv[6] if len(sys.argv) > 6 else 'same'
N, LP, PL, coord = load(q)
phi = np.fromfile(phif, dtype=np.int32).astype(np.int64)
assert phi.shape[0] == 2 * N
C = coord.astype(np.int64)
rng = np.random.default_rng(seed)
ADD, MUL, NEG, INV = gf_tables(q)
a = rng.integers(0, q, 7)
a2 = rng.integers(0, q, 7)
# polar form b(x,y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6 + x6y2 - 2 x3y3
PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
two = ADD[1][1]


def bform(x, y):
    acc = 0
    for i, j in PAIRS:
        acc = ADD[acc][MUL[x[i]][y[j]]]
    return ADD[acc][NEG[MUL[two][MUL[x[3]][y[3]]]]]


c = np.empty(N, dtype=np.int64)
nspec = 0
for p in range(N):
    s_, t_ = bform(C[p], a), bform(C[p], a2)
    if t_ != 0:
        c[p] = MUL[s_][INV[t_]]                # (s:t) = (s/t : 1) -> 0..q-1
    elif s_ != 0:
        c[p] = q                               # (1:0) = infinity
    else:
        c[p] = -1
        nspec += 1
spec = rng.integers(0, q + 1, N)
c = np.where(c < 0, spec, c)
f1 = 1 + c
f2 = q + 2 + c
with open(out, 'w') as f:
    f.write(f'Z {m}\n{2 * N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for l in range(N):
        for p in LP[l]:
            f.write(f'{p} {N + l} 0\n')
    for p in range(N):
        f.write(f'{p} {phi[p]} {f1[p] % m}\n')
        if mode == 'same':
            f.write(f'{p} {phi[p]} {f2[p] % m}\n')
    if mode == 'inv':
        for l in range(N):
            f.write(f'{phi[N + l]} {N + l} {f2[phi[N + l]] % m}\n')
print(f'q {q} m {m} points on the axis (c undefined): {nspec}', file=sys.stderr)

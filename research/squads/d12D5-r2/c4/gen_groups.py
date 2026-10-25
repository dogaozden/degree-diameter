#!/usr/bin/env python3
"""Group tables of order 70-84 for k=1 (c4). Uses groups.py (copied from research/d12D5) plus semidirect products Z_p^d x| Z_q."""
import sys, itertools
from groups import parse, check

def vid(v, p):
    return sum(x * p ** i for i, x in enumerate(v))

def matpow_apply(M, p, t, v):
    for _ in range(t):
        v = tuple(sum(M[r][c] * v[c] for c in range(len(v))) % p for r in range(len(v)))
    return v

def semi(p, d, M, q):
    """Z_p^d x| Z_q, generator of Z_q acts by matrix M (M^q = I mod p). element (v,t) -> index t*p^d + vid(v)."""
    vecs = list(itertools.product(range(p), repeat=d))
    vecs.sort(key=lambda v: vid(v, p))
    Mp = [[None] * (q) for _ in range(1)]
    powers = [tuple(tuple(int(i == j) for j in range(d)) for i in range(d))]
    cur = powers[0]
    for t in range(1, q):
        cur = tuple(tuple(sum(M[r][k] * cur[k][c] for k in range(d)) % p for c in range(d)) for r in range(d))
        powers.append(cur)
    # check M^q = I
    last = tuple(tuple(sum(M[r][k] * powers[-1][k][c] for k in range(d)) % p for c in range(d)) for r in range(d))
    assert last == tuple(tuple(int(i == j) for j in range(d)) for i in range(d)), 'M^q != I'
    el = [(v, t) for t in range(q) for v in vecs]
    idx = {e: i for i, e in enumerate(el)}
    def mul(a, b):
        (v, t), (w, s) = a, b
        Mt = powers[t]
        mw = tuple(sum(Mt[r][c] * w[c] for c in range(d)) % p for r in range(d))
        return (tuple((x + y) % p for x, y in zip(v, mw)), (t + s) % q)
    return [[idx[mul(a, b)] for b in el] for a in el]

def gf16_mul(a, b):
    r = 0
    for i in range(4):
        if (b >> i) & 1: r ^= a << i
    for i in (7, 6, 5, 4):
        if (r >> i) & 1: r ^= 0b10011 << (i - 4)
    return r

def frob16():
    beta = 1
    for _ in range(3): beta = gf16_mul(beta, 2)     # alpha = x, beta = alpha^3 (order 5)
    cols = [gf16_mul(beta, 1 << j) for j in range(4)]
    M = [[(cols[c] >> r) & 1 for c in range(4)] for r in range(4)]
    return M

def perm_table(gens):
    return parse(['perm', ';'.join(','.join(map(str, g)) for g in gens)])

SPECS = {
 # order 70
 'cyc70': 'cyc 70', 'dih35': 'dih 35', 'z5d7': 'prod cyc 5 / dih 7', 'z7d5': 'prod cyc 7 / dih 5', 'meta7_10_6': 'meta 7 10 6',
 # 71, 73, 77, 79, 83 (cyclic only)
 'cyc71': 'cyc 71', 'cyc73': 'cyc 73', 'cyc77': 'cyc 77', 'cyc79': 'cyc 79', 'cyc83': 'cyc 83',
 # 72
 'cyc72': 'cyc 72', 'dih36': 'dih 36', 'dicyc18': 'dicyc 18', 'z9m8': 'meta 9 8 8', 'z3d12': 'prod cyc 3 / dih 12',
 'z2dicyc9': 'prod cyc 2 / dicyc 9', 'm3_24': 'meta 3 24 2', 'm18_4': 'meta 18 4 17', 'm12_6_5': 'meta 12 6 5',
 'm12_6_7': 'meta 12 6 7', 'm6_12': 'meta 6 12 5', 'd9z4': 'prod dih 9 / cyc 4', 'd6z6': 'prod dih 6 / cyc 6',
 'd6s3': 'prod dih 6 / dih 3', 's3z12': 'prod dih 3 / cyc 12', 'd9x4b': 'prod dih 9 / dicyc 2',
 # 74
 'cyc74': 'cyc 74', 'dih37': 'dih 37',
 # 75
 'cyc75': 'cyc 75',
 # 76
 'cyc76': 'cyc 76', 'dih38': 'dih 38', 'dicyc19': 'dicyc 19', 'm19_4': 'meta 19 4 18', 'z2d19': 'prod cyc 2 / dih 19',
 # 78
 'dih39': 'dih 39', 'm13_6': 'meta 13 6 4', 'z3d13': 'prod cyc 3 / dih 13', 'z2m13_3': 'prod cyc 2 / meta 13 3 3',
 'cyc78': 'cyc 78', 'm26_3': 'meta 26 3 3', 'm3_26': 'meta 3 26 2',
 # 80
 'dih40': 'dih 40', 'm5_16_2': 'meta 5 16 2', 'm5_16_4': 'meta 5 16 4', 'm10_8_3': 'meta 10 8 3', 'm10_8_9': 'meta 10 8 9',
 'd10z4': 'prod dih 10 / cyc 4', 'd20z2': 'prod dih 20 / cyc 2', 'dic10z2': 'prod dicyc 10 / cyc 2', 'd5z8': 'prod dih 5 / cyc 8',
 'd5d4': 'prod dih 5 / dih 4', 'd5q8': 'prod dih 5 / dicyc 2',
 # 81
 'm9_9_4': 'meta 9 9 4', 'm27_3_10': 'meta 27 3 10', 'm27_3_19': 'meta 27 3 19', 'z3m9_3': 'prod cyc 3 / meta 9 3 4',
 # 82
 'dih41': 'dih 41', 'cyc82': 'cyc 82',
 # 84
 'dih42': 'dih 42', 'dicyc21': 'dicyc 21', 'm7_12_3': 'meta 7 12 3', 'm7_12_2': 'meta 7 12 2', 'm21_4_20': 'meta 21 4 20',
 'm21_4_8': 'meta 21 4 8', 'm14_6_3': 'meta 14 6 3', 'm14_6_9': 'meta 14 6 9', 'z3d14': 'prod cyc 3 / dih 14',
 'd21z2': 'prod dih 21 / cyc 2', 'f42z2': 'prod meta 7 6 3 / cyc 2', 's3d7': 'prod dih 3 / dih 7', 'd7z6': 'prod dih 7 / cyc 6',
 'd6z7': 'prod dih 6 / cyc 7', 'cyc84': 'cyc 84',
}
ORDER_CHECK = {}
PERM = {
 'wr33': [[1,2,0,3,4,5,6,7,8],[3,4,5,6,7,8,0,1,2]],     # Z_3 wr Z_3 (order 81)
 'a4z6': None,
}
def build(name):
    if name == 'semi_f75':
        return semi(5, 2, [[0, 4], [1, 4]], 3)
    if name == 'semi_f80':
        return semi(2, 4, frob16(), 5)
    if name == 'semi_f72':
        return semi(3, 2, [[1, 2], [1, 1]], 8)
    if name == 'semi_j81':
        return semi(3, 3, [[1, 1, 0], [0, 1, 1], [0, 0, 1]], 3)
    if name == 'wr33':
        return perm_table(PERM['wr33'])
    if name == 'a4z6':
        return parse(['prod', 'perm', '1,2,0,3;1,0,3,2', '/', 'cyc', '6'])
    if name in SPECS:
        return parse(SPECS[name].split())
    raise KeyError(name)

if __name__ == '__main__':
    names = sys.argv[1:] or (list(SPECS) + ['semi_f75', 'semi_f80', 'semi_f72', 'semi_j81', 'wr33', 'a4z6'])
    for name in names:
        T = build(name); n = len(T)
        e = check(T)
        # full associativity check (groups.py only samples)
        ok = all(T[T[a][b]][c] == T[a][T[b][c]] for a in range(n) for b in range(n) for c in range(n))
        assert ok, name
        with open(f'tables/{name}.txt', 'w') as f:
            f.write(f"{n}\n" + ' '.join(str(x) for row in T for x in row) + '\n')
        print(name, n, 'OK' if 70 <= n <= 84 else 'OUT_OF_RANGE', flush=True)

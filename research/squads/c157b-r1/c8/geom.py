#!/usr/bin/env python3
"""geom.py: load H(11) (points as PG(6,11) coords, lines as 12 point ids) and provide hyperplane helpers."""
import numpy as np, os
HEX = '/home/user/degree-diameter/research/squads/c157b-r1/shared/hex_q11.bin'
q = 11

def load():
    b = open(HEX, 'rb').read()
    qq, N, L = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
    assert qq == q
    LP = np.frombuffer(b[12:12 + 4 * L * 12], dtype=np.int32).reshape(L, 12).astype(np.int64)
    off = 12 + 4 * L * 12
    C = np.frombuffer(b[off:off + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return N, L, LP, C

def pl_table(N, L, LP):
    # PL[p] = the 12 lines through point p
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(L), 12)
    order = np.lexsort((flat_l, flat_p))
    return flat_l[order].reshape(N, 12)

if __name__ == '__main__':
    N, L, LP, C = load()
    # check quadric X0X4+X1X5+X2X6 = X3^2 mod 11
    Qv = (C[:, 0] * C[:, 4] + C[:, 1] * C[:, 5] + C[:, 2] * C[:, 6] - C[:, 3] * C[:, 3]) % q
    print('quadric ok:', bool((Qv == 0).all()), 'N', N, 'L', L)
    PL = pl_table(N, L, LP)
    print('lines per point:', np.unique(np.bincount(LP.reshape(-1), minlength=N)))

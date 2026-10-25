#!/usr/bin/env python3
"""gperm.py: permutations of the points and lines of H(11) induced by a collineation, for orbit (symmetric) searches.
Point ids are the rows of the coordinate table in hex_q11.bin (points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,11), first
nonzero coordinate 1); line ids are the rows of the line table.
  python3 gperm.py sl3 a b c d e f g h i OUTPREFIX     g in SL(3,11) acting as (v, a, w) -> (g v, a, g^-T w),
                                                        v = (X0,X1,X2), a = X3, w = (X4,X5,X6)
  python3 gperm.py mat7 m00 ... m66 OUTPREFIX          any 7x7 matrix over F_11 (checked to map lines to lines)
writes OUTPREFIX_pts.txt and OUTPREFIX_lines.txt (image of id i on line i) and prints the orbit-size counts.
As a module: perm_from_mat7(M) -> (point perm, line perm) or raises if M is not a collineation of H(11)."""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
b = open(os.path.join(HERE, 'hex_q11.bin'), 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
code = X @ (q ** np.arange(7, dtype=np.int64))
inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)


def perm_from_mat7(M):
    M = np.asarray(M, dtype=np.int64) % q
    Y = (X @ M.T) % q
    if (Y == 0).all(1).any(): raise ValueError('singular')
    lead = np.argmax(Y != 0, axis=1)
    Y = (Y * inv[Y[np.arange(N), lead]][:, None]) % q
    c = Y @ (q ** np.arange(7, dtype=np.int64))
    pp = np.searchsorted(code, c)
    if not (pp < N).all() or not (code[np.minimum(pp, N - 1)] == c).all(): raise ValueError('does not preserve the quadric')
    if len(np.unique(pp)) != N: raise ValueError('not a bijection')
    a0, b0 = pp[LP[:, 0]], pp[LP[:, 1]]
    hit = (PL[a0][:, :, None] == PL[b0][:, None, :]).reshape(Lc, -1)
    if not (hit.sum(1) == 1).all(): raise ValueError('does not map lines to lines')
    lp = PL[a0, hit.argmax(axis=1) // Q1]
    # all q+1 points of every line must land on the image line
    if not (np.sort(pp[LP], 1) == np.sort(LP[lp], 1)).all(): raise ValueError('does not map lines to lines')
    return pp, lp


def sl3_to_mat7(g):
    g = np.asarray(g, dtype=np.int64).reshape(3, 3) % q
    det = int(round(np.linalg.det(g))) % q
    adj = np.array([[((g[(j + 1) % 3][(i + 1) % 3] * g[(j + 2) % 3][(i + 2) % 3]
                       - g[(j + 1) % 3][(i + 2) % 3] * g[(j + 2) % 3][(i + 1) % 3])) % q for j in range(3)]
                    for i in range(3)], dtype=np.int64)
    gi = (adj * pow(det, q - 2, q)) % q
    M = np.zeros((7, 7), np.int64); M[0:3, 0:3] = g; M[3, 3] = 1; M[4:7, 4:7] = gi.T
    return M


def orbit_sizes(p):
    seen = np.zeros(len(p), bool); sz = {}
    for i in range(len(p)):
        if seen[i]: continue
        k = 0; j = i
        while not seen[j]: seen[j] = True; j = p[j]; k += 1
        sz[k] = sz.get(k, 0) + 1
    return dict(sorted(sz.items()))


if __name__ == '__main__':
    kind = sys.argv[1]
    if kind == 'sl3':
        M = sl3_to_mat7([int(x) for x in sys.argv[2:11]]); out = sys.argv[11]
    else:
        M = np.array([int(x) for x in sys.argv[2:51]]).reshape(7, 7); out = sys.argv[51]
    pp, lp = perm_from_mat7(M)
    np.savetxt(out + '_pts.txt', pp, fmt='%d'); np.savetxt(out + '_lines.txt', lp, fmt='%d')
    print('collineation OK; point cycle sizes', orbit_sizes(pp), 'line cycle sizes', orbit_sizes(lp))

"""certify.py LINES.txt [HEXBIN]: independent check of a set of pairwise disjoint totally singular lines of Q(6,11).

Reads only the raw coordinates of hex_q11.bin (ids = row index) and the stated quadric
Q(x) = x0x4 + x1x5 + x2x6 - x3^2 with polar form b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (mod 11).
Each text line must hold q+1 = 12 distinct point ids; the 12 points must be singular, pairwise orthogonal
and span a 2-dimensional subspace (a projective line, all 12 of its points). Lines must be pairwise disjoint.
Prints the number of certified lines and VALID / INVALID.
"""
import struct
import sys
import numpy as np

Q = 11
HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q11.bin'


def rank_mod_p(M):
    M = [list(map(int, r)) for r in M]
    rk = 0
    rows, cols = len(M), len(M[0])
    for c in range(cols):
        piv = None
        for r in range(rk, rows):
            if M[r][c] % Q:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c] % Q, Q - 2, Q)
        M[rk] = [(v * inv) % Q for v in M[rk]]
        for r in range(rows):
            if r != rk and M[r][c] % Q:
                f = M[r][c]
                M[r] = [(a - f * b) % Q for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk


def main():
    lines_path = sys.argv[1]
    hexbin = sys.argv[2] if len(sys.argv) > 2 else HEX
    with open(hexbin, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12))
        assert q == Q
        f.seek(12 + 4 * L * (Q + 1))
        X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
    # form matrix B with x^T B y = b(x,y)
    B = np.zeros((7, 7), dtype=np.int64)
    for i, j in ((0, 4), (1, 5), (2, 6)):
        B[i, j] = B[j, i] = 1
    B[3, 3] = -2
    Qv = (X[:, 0] * X[:, 4] + X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % Q
    assert (Qv == 0).all() or True  # checked per line below (all points used are checked)

    seen_pts = {}
    good = 0
    bad_reasons = {}
    lines = []
    with open(lines_path) as f:
        for ln, text in enumerate(f):
            parts = text.split()
            if not parts:
                continue
            ids = [int(v) for v in parts]
            lines.append((ln, ids))
    for ln, ids in lines:
        reason = None
        if len(ids) != Q + 1:
            reason = 'size'
        elif len(set(ids)) != Q + 1:
            reason = 'repeated point'
        elif min(ids) < 0 or max(ids) >= N:
            reason = 'id out of range'
        else:
            M = X[ids]
            if ((np.einsum('ij,jk,ik->i', M, B, M)) % Q != 0).any():
                reason = 'not totally singular (x^T B x != 0)'
            else:
                G = (M @ B @ M.T) % Q
                if (G != 0).any():
                    reason = 'points not pairwise orthogonal'
                elif rank_mod_p(M) != 2:
                    reason = 'points do not span a line'
        if reason is None:
            clash = [p for p in ids if p in seen_pts]
            if clash:
                reason = 'shares point with an earlier line (line %d)' % seen_pts[clash[0]]
        if reason is not None:
            bad_reasons[reason] = bad_reasons.get(reason, 0) + 1
            continue
        for p in ids:
            seen_pts[p] = ln
        good += 1
    print('lines read:', len(lines), ' certified:', good, ' rejected:', bad_reasons)
    print('distinct points covered:', len(seen_pts), 'of', N, '(bound', N // (Q + 1), 'lines)')
    print('VALID' if good == len(lines) and len(lines) > 0 else 'INVALID')
    print('certified count:', good)


if __name__ == '__main__':
    main()

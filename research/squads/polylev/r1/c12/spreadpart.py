"""spreadpart.py: look for a partition of the lines of H(q) into spreads, as the orbit of one spread under a
Singer subgroup C (order q^2+q+1) of SL(3,q) <= G_2(q).

1. g: an element of SL(3,q) of order k = q^2+q+1 (random search; order tested by the primes of k).
   C = <g> acts on Q(6,q) by (v, a, w) -> (g v, a, g^{-T} w); we check that it maps lines of H(q) to lines.
2. A spread S: the lines of H(q) inside a hyperplane ker(f) (f a random linear form), kept when there are q^3+1 of
   them and they are pairwise opposite (no common point and no common neighbour line, i.e. distance 6).
3. The translates g^i S, i < k, are tested for disjointness; disjoint translates partition the lines.
Writes: <out>.lineclass (L ints: class of each line), <out>.g (the matrix), and prints a summary.
Usage: python3 spreadpart.py HEXBIN OUT [seed] [tries]
"""
import sys
import numpy as np
from hexlib import Hex


def primes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def mat_pow(H, A, n):
    R = np.eye(3, dtype=np.int64)
    B = A.copy()
    while n:
        if n & 1:
            R = H.mat_mul(R, B)
        B = H.mat_mul(B, B)
        n >>= 1
    return R


def is_scalar(M):
    return M[0, 1] == M[0, 2] == M[1, 0] == M[1, 2] == M[2, 0] == M[2, 1] == 0 and M[0, 0] == M[1, 1] == M[2, 2]


def find_singer(H, rng):
    q = H.q
    k = q * q + q + 1
    I = np.eye(3, dtype=np.int64)
    while True:
        g = rng.integers(0, q, size=(3, 3))
        d = H.det3(g)
        if d == 0:
            continue
        # scale the first row so that det = 1
        g[0] = H.MUL[H.INV[d], g[0]]
        if H.det3(g) != 1:
            continue
        if not (mat_pow(H, g, k) == I).all():
            continue
        if any(is_scalar(mat_pow(H, g, k // p)) for p in primes(k)):
            continue
        return g


def opposite_lines_ok(H, S):
    """S pairwise opposite: no shared point, and no line meets two of them (distance >= 6)."""
    pts = H.lines[S].ravel()
    if len(np.unique(pts)) != len(pts):
        return False
    owner = -np.ones(H.N, dtype=np.int64)
    for i, l in enumerate(S):
        owner[H.lines[l]] = i
    # a line meeting two spread lines: check each line's points have at most one owner
    own = owner[H.lines]
    for row in own:
        r = row[row >= 0]
        if len(np.unique(r)) > 1:
            return False
    return True


def main():
    hexbin, out = sys.argv[1], sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    tries = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    rng = np.random.default_rng(seed)
    H = Hex(hexbin)
    q, N, L = H.q, H.N, H.L
    k = q * q + q + 1
    g = find_singer(H, rng)
    pm = H.sl3_point_map(g)
    lm = H.line_map(pm)          # raises if C does not preserve H(q)
    # orbits of C on lines (semiregular?)
    seen = -np.ones(L, dtype=np.int64)
    norb = 0
    for l in range(L):
        if seen[l] >= 0:
            continue
        x, c = l, 0
        while seen[x] < 0:
            seen[x] = norb
            x = lm[x]
            c += 1
        if c != k:
            print(f'line orbit of size {c} (not semiregular)')
        norb += 1
    print(f'q={q} k={k} g={g.tolist()} line orbits {norb} (expect {L // k})')
    found = None
    for t in range(tries):
        f = rng.integers(0, q, size=7)
        if not f.any():
            continue
        # lines in ker f: both of the first two points satisfy f.x = 0
        P2 = H.coord
        val = np.zeros(N, dtype=np.int64)
        for j in range(7):
            val = H.ADD[val, H.MUL[f[j], P2[:, j]]]
        inker = val == 0
        S = np.where(inker[H.lines].all(axis=1))[0]
        if len(S) != q ** 3 + 1 or not opposite_lines_ok(H, S):
            continue
        # translates
        cls = -np.ones(L, dtype=np.int64)
        cur = S.copy()
        ok = True
        for i in range(k):
            if (cls[cur] >= 0).any():
                ok = False
                break
            cls[cur] = i
            cur = lm[cur]
        print(f'try {t}: spread in ker f, f={f.tolist()}, translates disjoint: {ok}')
        if ok:
            found = (f, cls)
            break
    if found is None:
        print('no partition found')
        return
    f, cls = found
    assert (cls >= 0).all()
    # verify: every line 2-ball (the line and the lines meeting it) contains each class exactly once
    bad = 0
    for l in range(L):
        ball = set([l])
        for x in H.lines[l]:
            ball.update(H.PL[x].tolist())
        if sorted(cls[list(ball)].tolist()) != list(range(k)):
            bad += 1
    print(f'line 2-balls rainbow: {L - bad}/{L}')
    cls.astype(np.int32).tofile(out + '.lineclass')
    np.savetxt(out + '.g', g, fmt='%d')
    with open(out + '.f', 'w') as fh:
        fh.write(' '.join(map(str, f.tolist())) + '\n')


if __name__ == '__main__':
    main()

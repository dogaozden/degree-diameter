#!/usr/bin/env python3
# Builds line-orbit labels for named collineation groups of H(11) (c5 card, lines).
# usage: python3 mkgroups.py NAME   -> writes c5/lab_NAME.bin (int32 per line = orbit id) and prints a summary.
import sys, os, numpy as np
SH = '/home/user/degree-diameter/research/squads/c157b-r1/shared'
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SH)
import gperm
q = 11
L = gperm.Lc
G133 = np.array([[8, 1, 10], [0, 8, 1], [7, 4, 4]], dtype=np.int64)


def mm(A, B): return (np.asarray(A, np.int64) @ np.asarray(B, np.int64)) % q


def mpow(A, k):
    R = np.eye(3, dtype=np.int64); B = np.asarray(A, np.int64) % q
    while k:
        if k & 1: R = mm(R, B)
        B = mm(B, B); k >>= 1
    return R


def det3(A):
    A = [[int(x) % q for x in r] for r in A]
    d = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
         + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    return d % q


def order3(A, maxo=2000):
    B = np.asarray(A, np.int64) % q; M = B.copy(); I = np.eye(3, dtype=np.int64)
    for k in range(1, maxo + 1):
        if (M == I).all(): return k
        M = mm(M, B)
    return None


def nullspace_mod(A, p=q):
    A = [[x % p for x in row] for row in A]
    m, n = len(A), len(A[0]); piv = []; r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i][c]), None)
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]
        inv = pow(A[r][c], p - 2, p); A[r] = [(x * inv) % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c]:
                f = A[i][c]; A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(n)]
        piv.append(c); r += 1
        if r == m: break
    basis = []
    for fc in [c for c in range(n) if c not in piv]:
        v = [0] * n; v[fc] = 1
        for i, pc in enumerate(piv): v[pc] = (-A[i][fc]) % p
        basis.append(v)
    return basis


def phi_normaliser(g, k):
    """H with H g H^-1 = g^k, det 1, order 3 (random element of the intertwiner space)."""
    G = mpow(g, k)
    A = [[0] * 9 for _ in range(9)]
    for i in range(3):
        for j in range(3):
            for a in range(3):
                for b in range(3):
                    A[3 * i + j][3 * a + b] = ((1 if i == a else 0) * int(g[b][j]) - int(G[i][a]) * (1 if b == j else 0)) % q
    B = nullspace_mod(A)
    rng = np.random.default_rng(1)
    for _ in range(20000):
        c = rng.integers(0, q, len(B))
        v = [sum(int(c[t]) * B[t][s] for t in range(len(B))) % q for s in range(9)]
        H = np.array(v, np.int64).reshape(3, 3)
        if det3(H) == 1 and order3(H) == 3:
            return H
    raise RuntimeError('no phi found')


def elem_order120():
    # companion matrix of x^2 - t x + n irreducible with primitive root lambda; block diag(M, 1/n)
    for t in range(q):
        for n in range(1, q):
            if all((x * x - t * x + n) % q for x in range(q)):
                M = np.array([[0, (-n) % q], [1, t]], np.int64)
                I2 = np.eye(2, dtype=np.int64)
                def p2(k):
                    R = I2.copy(); B = M.copy()
                    while k:
                        if k & 1: R = (R @ B) % q
                        B = (B @ B) % q; k >>= 1
                    return R
                if (p2(120) == I2).all() and not (p2(60) == I2).all() and not (p2(40) == I2).all() and not (p2(24) == I2).all():
                    dinv = pow(n, q - 2, q)
                    H = np.zeros((3, 3), np.int64); H[0:2, 0:2] = M; H[2, 2] = dinv
                    assert det3(H) == 1
                    return H
    raise RuntimeError


def elem_order110():
    a = 2  # primitive root mod 11
    s = [a, pow(a, q - 3, q), a]           # diag(a, a^-2, a)
    H = np.diag(s).astype(np.int64); H[0, 2] = s[0]
    assert det3(H) == 1
    return H


def swap_mat7():
    M = np.zeros((7, 7), np.int64)
    M[0:3, 4:7] = np.eye(3, dtype=np.int64); M[3, 3] = q - 1; M[4:7, 0:3] = np.eye(3, dtype=np.int64)
    return M


def perms_for(gen):
    if isinstance(gen, str) and gen == 'swap':
        return gperm.perm_from_mat7(swap_mat7())
    return gperm.perm_from_mat7(gperm.sl3_to_mat7(np.asarray(gen).reshape(-1)))


def labels_from(lps):
    parent = list(range(L))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for p in lps:
        for i, j in enumerate(p.tolist()):
            if i != j:
                a, b = find(i), find(j)
                if a != b: parent[a] = b
    roots = np.array([find(i) for i in range(L)], np.int64)
    _, lab = np.unique(roots, return_inverse=True)
    return lab.astype(np.int32)


def main():
    name = sys.argv[1]
    g = G133
    phi = phi_normaliser(g, 11)
    h120 = elem_order120()
    h110 = elem_order110()
    gens = {
        'g133': [g],
        'g399': [g, phi],
        'c120': [h120],
        'c110': [h110],
        'c60': [mpow(h120, 2)],
        'c40': [mpow(h120, 3)],
        'c24': [mpow(h120, 5)],
        'c12': [mpow(h120, 10)],
        'sw_g': [g, 'swap'],
        'sw_g_phi': [g, phi, 'swap'],
        'sw_c120': [h120, 'swap'],
        'c120_c110': [h120, h110],
        'c55': [mpow(h110, 2)],
        'c22': [mpow(h110, 5)],
        'c11': [mpow(h110, 10)],
        'sl2': [np.array([[1, 1, 0], [0, 1, 0], [0, 0, 1]]), np.array([[0, 1, 0], [10, 0, 0], [0, 0, 1]])],
        'u3': [np.array([[1, 1, 0], [0, 1, 0], [0, 0, 1]]), np.array([[1, 0, 0], [0, 1, 1], [0, 0, 1]])],
        't100': [np.diag([2, 6, 1]), np.diag([1, 2, 6])],
        'dt200': [np.diag([2, 6, 1]), np.diag([1, 2, 6]), 'swap'],
    }[name]
    print('group', name, 'order-3 phi found; order(g)=', order3(g, 2000), 'order(h120)=', order3(h120, 2000), 'order(h110)=', order3(h110, 2000))
    lps = []
    for gen in gens:
        pp, lp = perms_for(gen)
        lps.append(lp)
    lab = labels_from(lps)
    lab.tofile(os.path.join(HERE, 'lab_%s.bin' % name))
    K = int(lab.max()) + 1
    sz = np.bincount(lab, minlength=K)
    hist = {}
    for s in sz.tolist(): hist[s] = hist.get(s, 0) + 1
    print('orbits on lines:', K, ' size histogram:', dict(sorted(hist.items())))
    print('written', os.path.join(HERE, 'lab_%s.bin' % name))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Card c2 (squad round 6): the normaliser of <h> in O(7,11), h = a b^2, and which of its elements keep the 756 set.

Structure (checked in the run): a|U has characteristic polynomial (x-1)(x-3)(x-4)(x^2+x+1) over F_11, so h has the
eigenvalues w, w^2 (w a cube root of unity, on a non-degenerate 2-dim block B1) and 1, 3, 4, 5, 9 (1-dim eigenlines
E1, E3, E4, E5, E9 inside B1-perp).  g normalises <h> iff g preserves B1 and B1-perp, so N(<h>) = N1 x N2 with
N1 = N_{O(B1)}(h|B1) and N2 = N_{O(B1perp)}(h|B1perp).  Both are enumerated here by brute force in eigen-bases.
usage: normaliser.py    (writes norm_elements.npz with the 7x7 matrices of N and the stabiliser of the 756 set)"""
import itertools
import os
import sys

import numpy as np

from common import HERE, L, MMUL, MPOW, h_matrix, read_points

p = 11
J = L.J
I7 = L.I7
P = L.P
CODES = L.CODES


def nullspace(M):
    return L.nullspace_mod(M % p)


def mp(M, e):
    n = M.shape[0]
    R = np.eye(n, dtype=np.int64)
    B = M.copy() % p
    while e:
        if e & 1:
            R = (R @ B) % p
        B = (B @ B) % p
        e >>= 1
    return R


def inv_mod(M):
    n = M.shape[0]
    A = np.concatenate([M % p, np.eye(n, dtype=np.int64)], axis=1)
    r = 0
    for c in range(n):
        pr = next(i for i in range(r, n) if A[i, c] % p)
        A[[r, pr]] = A[[pr, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        for i in range(n):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
    return A[:, n:]


def main():
    h = h_matrix()
    # eigen-decomposition of h over F_11
    B1 = nullspace((MMUL(h, h) + h + I7) % p)            # rows: basis of the omega-block (dim 2)
    lines = {}
    for x in [1, 3, 4, 5, 9]:
        E = nullspace((h - x * I7) % p)
        assert E.shape[0] == 1, (x, E.shape)
        lines[x] = E[0]
    assert B1.shape[0] == 2
    Q = np.concatenate([B1, np.array([lines[x] for x in [1, 3, 4, 5, 9]])], axis=0).T % p   # columns
    assert np.linalg.matrix_rank(Q.astype(float)) == 7 or True
    Qi = inv_mod(Q)
    hQ = MMUL(MMUL(Qi, h), Q)
    print('h in eigen-basis (block form):\n', hQ)
    # isometry check for elements written in the eigen-basis: g = Q gQ Q^-1 ; isometry: g^T J g = J
    Gram_Q = MMUL(MMUL(Q.T, J), Q) % p     # Gram matrix in the eigen-basis
    print('Gram in eigen-basis:\n', Gram_Q)

    # ---- N1: 2x2 blocks on B1 (indices 0,1) ----
    h3 = hQ[:2, :2]                         # h on B1 in the basis (B1 is invariant)
    assert np.array_equal(hQ[2:, :2] % p, np.zeros((5, 2), np.int64))
    G1 = Gram_Q[:2, :2]
    N1 = []
    for ent in itertools.product(range(p), repeat=4):
        M = np.array(ent, dtype=np.int64).reshape(2, 2)
        if int(round(np.linalg.det(M.astype(float)))) % p == 0:
            continue
        if not np.array_equal(MMUL(M.T, MMUL(G1, M)) % p, G1 % p):
            continue
        if any(np.array_equal(MMUL(M, h3) % p, MMUL(mp(h3, j), M) % p) for j in (1, 2)):
            N1.append(M)
    print('|N1 candidates| =', len(N1))

    # ---- N2: monomial matrices on the five eigenlines (1,3,4,5,9) ----
    xs = [1, 3, 4, 5, 9]
    # h restricted to B1-perp is diagonal diag(1,3,4,5,9) in this basis
    d5 = np.diag(hQ[2:, 2:]) % p
    assert np.array_equal(hQ[2:, 2:] % p, np.diag(d5))
    # h_5 = diag(d5); multiplier m in F_5^*: h5^m has eigenvalue x^m on line x.  Need pi: lines x -> y with y^m = x?
    # we want g h5 g^-1 = h5^m: g maps the eigenline of eigenvalue x to the eigenline of eigenvalue x^(1/m).
    N2 = []
    G2 = Gram_Q[2:, 2:]
    for m in [1, 2, 3, 4]:
        # eigenvalue x^(1/m) : m is an exponent mod 5, invert it mod 5
        minv = pow(m, -1 , 5)
        perm = []
        for x in d5:
            y = int(pow(int(x), minv, p))
            perm.append(int(np.flatnonzero(d5 == y)[0]))
        # g e_i = d_i e_{perm[i]} ; matrix M with M[perm[i], i] = d_i
        for dvals in itertools.product(range(1, p), repeat=5):
            M = np.zeros((5, 5), dtype=np.int64)
            for i in range(5):
                M[perm[i], i] = dvals[i]
            if np.array_equal(MMUL(M.T, MMUL(G2, M)) % p, G2 % p):
                # check normalising: M diag(d5) M^-1 = diag(d5)^m
                Mi = inv_mod(M)
                lhs = MMUL(MMUL(M, np.diag(d5)), Mi) % p
                rhs = np.diag(np.array([pow(int(x), m, p) for x in d5], dtype=np.int64)) % p
                if np.array_equal(lhs, rhs):
                    N2.append((m, M))
    print('|N2| =', len(N2))
    # ---- assemble full group elements in the standard basis ----
    elems = []
    for M1 in N1:
        for m, M2 in N2:
            gQ = np.zeros((7, 7), dtype=np.int64)
            gQ[:2, :2] = M1
            gQ[2:, 2:] = M2
            g = MMUL(MMUL(Q, gQ), Qi)
            elems.append((g, m))
    print('|N| =', len(elems))
    # stabiliser of the 756 set
    S = read_points(os.path.join(HERE, '..', '..', 'd13D7_r4', 'c1', 'best_idx.txt'))
    XS = P[S]
    Sset = np.sort(S)
    stab = []
    for g, m in elems:
        Y = (XS @ g.T) % p
        lead_idx = (Y != 0).argmax(axis=1)
        lead = Y[np.arange(Y.shape[0]), lead_idx]
        Y = (Y * np.array(L.INV)[lead][:, None]) % p
        codes = Y @ L.PW
        idx = np.searchsorted(CODES, codes)
        if np.array_equal(np.sort(idx), Sset):
            stab.append((g, m))
    print('stabiliser of the 756 set inside N: order', len(stab), ' multipliers', sorted(set(m for _, m in stab)))
    # which are in <h>?
    hp = [MPOW(h, k) for k in range(15)]  # 7x7 powers
    inh = [any(np.array_equal(g, hk) or np.array_equal(g, (-hk) % p) for hk in hp) for g, _ in stab]
    print('stabiliser elements inside <h> (or -<h>):', sum(inh))
    np.savez(os.path.join(HERE, 'norm_stab.npz'), mats=np.array([g for g, _ in stab]), mult=np.array([m for _, m in stab]))
    np.savez(os.path.join(HERE, 'norm_all.npz'), mats=np.array([g for g, _ in elems]), mult=np.array([m for _, m in elems]))


if __name__ == '__main__':
    main()

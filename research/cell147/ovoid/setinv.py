#!/usr/bin/env python3
"""Isometry invariants of a point set of Q(6,q): diag of S^3 where S = chi(B(x,y)) (quadratic character, scale-free
in triples), and the size distribution of hyperplane-section intersections is too slow, so we use S^3 and S^2*S."""
import sys, numpy as np, collections
q = 11
def load(f):
    X = np.loadtxt(f, dtype=np.int64, comments='#') % q
    return X
def chi_matrix(X):
    Y = X[:, [4, 5, 6, 3, 0, 1, 2]].copy(); Y[:, 3] = (-2 * Y[:, 3]) % q
    Bm = (X @ Y.T) % q
    sq = np.zeros(q, dtype=np.int64); 
    for a in range(1, q): sq[a * a % q] = 1
    S = np.where(Bm == 0, 0, np.where(sq[Bm] == 1, 1, -1))
    np.fill_diagonal(S, 0)
    return S
for f in sys.argv[1:]:
    X = load(f); S = chi_matrix(X).astype(np.int64)
    d3 = np.diag(S @ S @ S)
    c = collections.Counter(d3.tolist())
    print(f, len(X), 'trace S^3 =', int(d3.sum()), 'diag(S^3) distribution:', sorted(c.items())[:12])

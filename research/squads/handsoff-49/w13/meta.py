"""Metacyclic groups Z_m x|_r Z_k as numpy multiplication tables; index a + m*j; (a,j)(b,l)=(a+r^j b, j+l)."""
import numpy as np

def meta_table(m, k, r):
    N = m * k
    assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a = g % m; j = g // m
    A = a[:, None]; J = j[:, None]
    B = a[None, :]; L = j[None, :]
    na = (A + rp[J] * B) % m
    nj = (J + L) % k
    return (na + m * nj).astype(np.int32)

def inverses(T):
    N = T.shape[0]
    return np.argmax(T == 0, axis=1).astype(np.int32)

def prodset(T, X, Y):
    """set {x*y : x in X, y in Y} as sorted unique array"""
    X = np.asarray(X, dtype=np.int64); Y = np.asarray(Y, dtype=np.int64)
    return np.unique(T[np.ix_(X, Y)].ravel())

def T_of_S(T, Sinv, S):
    """T = S^{-1} S as sorted unique array"""
    return prodset(T, Sinv[np.asarray(S)], np.asarray(S))

def far_set(T, S, Sinv=None, reps=4):
    """elements of G not in (S^{-1}S)^reps (same-side far set, from root e)"""
    if Sinv is None:
        Sinv = inverses(T)
    Tset = T_of_S(T, Sinv, S)
    P = np.array([0], dtype=np.int64)
    for _ in range(reps):
        P = prodset(T, P, Tset)
    N = T.shape[0]
    mask = np.ones(N, dtype=bool); mask[P] = False
    return np.nonzero(mask)[0]

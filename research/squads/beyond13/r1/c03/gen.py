#!/usr/bin/env python3
"""gen.py NAME OUT.bin : multiplication table of a group, identity = index 0.
Binary format: int32 N, then N*N uint16 with T[g*N+h] = index of g*h.
Names: psl:P sl:P pgl:P (P prime >= 5), perm:A6|S6|A5|S5, prod:<base>:n:<cycle order n>, with <base> another name
(the product is base x Z_n); product of two names: prod2:<nameA>:<nameB>."""
import sys, numpy as np

def mats(p, kind):
    r = np.arange(p)
    a, b, c, d = [x.ravel() for x in np.meshgrid(r, r, r, r, indexing='ij')]
    det = (a * d - b * c) % p
    mask = (det == 1) if kind in ('sl', 'psl') else (det != 0)
    return np.stack([a, b, c, d], 1)[mask].astype(np.int64)

def code(M, p):
    return ((M[:, 0] * p + M[:, 1]) * p + M[:, 2]) * p + M[:, 3]

def canon(M, p, kind):
    if kind in ('sl',):
        return M
    if kind == 'psl':
        N2 = (-M) % p
        return np.where((code(M, p) <= code(N2, p))[:, None], M, N2)
    invt = np.zeros(p, dtype=np.int64)
    for x in range(1, p):
        invt[x] = pow(x, p - 2, p)
    f = np.argmax(M != 0, axis=1)
    lead = M[np.arange(len(M)), f]
    return (M * invt[lead][:, None]) % p

def matgroup(p, kind):
    M = canon(mats(p, kind), p, kind)
    codes = np.unique(code(M, p))
    def dec(c):
        c = c.copy(); d = c % p; c //= p; cc = c % p; c //= p; b = c % p; c //= p
        return np.stack([c % p, b, cc, d], 1)
    E = dec(codes)
    N = len(codes)
    T = np.zeros((N, N), dtype=np.int64)
    for g in range(N):
        X = np.broadcast_to(E[g], E.shape)
        a1, b1, c1, d1 = X[:, 0], X[:, 1], X[:, 2], X[:, 3]
        a2, b2, c2, d2 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
        P = np.stack([(a1 * a2 + b1 * c2) % p, (a1 * b2 + b1 * d2) % p,
                      (c1 * a2 + d1 * c2) % p, (c1 * b2 + d1 * d2) % p], 1)
        P = canon(P, p, kind)
        T[g] = np.searchsorted(codes, code(P, p))
    return T

def perm_closure(gens):
    n = len(gens[0])
    idt = tuple(range(n))
    els = [idt]; seen = {idt: 0}; i = 0
    while i < len(els):
        g = els[i]; i += 1
        for s in gens:
            h = tuple(g[s[j]] for j in range(n))
            if h not in seen:
                seen[h] = len(els); els.append(h)
    N = len(els)
    T = np.zeros((N, N), dtype=np.int64)
    for a, g in enumerate(els):
        for b, h in enumerate(els):
            T[a, b] = seen[tuple(g[h[j]] for j in range(n))]
    return T

def perm_group(name):
    if name == 'A5':
        return perm_closure([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])
    if name == 'S5':
        return perm_closure([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)])
    if name == 'A6':
        return perm_closure([(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)])
    if name == 'S6':
        return perm_closure([(1, 0, 2, 3, 4, 5), (1, 2, 3, 4, 5, 0)])
    raise ValueError(name)

def to_identity0(T):
    N = len(T)
    e = [g for g in range(N) if (T[g] == np.arange(N)).all()][0]
    perm = np.arange(N); perm[[0, e]] = [e, 0]   # new index i -> old index perm[i]
    inv = np.argsort(perm)                       # old -> new
    T2 = inv[T[np.ix_(perm, perm)]]
    return T2

def cyc_prod(T1, n):
    N = len(T1)
    K = np.arange(n)
    S = (K[:, None] + K[None, :]) % n
    A = T1[:, None, :, None] * n                 # (N,1,N,1)
    R = A + S[None, :, None, :]                  # (N,n,N,n)
    return R.reshape(N * n, N * n)

def direct(T1, T2):
    N1, N2 = len(T1), len(T2)
    A = T1[:, None, :, None] * N2
    B = T2[None, :, None, :]
    return (A + B).reshape(N1 * N2, N1 * N2)

def build(name):
    if name.startswith('psl:'): return to_identity0(matgroup(int(name[4:]), 'psl'))
    if name.startswith('sl:'): return to_identity0(matgroup(int(name[3:]), 'sl'))
    if name.startswith('pgl:'): return to_identity0(matgroup(int(name[4:]), 'pgl'))
    if name.startswith('perm:'): return to_identity0(perm_group(name[5:]))
    if name.startswith('x'):   # 'x<n>(<base>)' = base x Z_n
        n, rest = name[1:].split('(', 1)
        return to_identity0(cyc_prod(build(rest[:-1]), int(n)))
    if name.startswith('d[') and name.endswith(']'):   # d[A|B] direct product
        a, b = name[2:-1].split('|', 1)
        return to_identity0(direct(build(a), build(b)))
    raise ValueError(name)

def cyc(n):
    return (np.arange(n)[:, None] + np.arange(n)[None, :]) % n

if __name__ == '__main__':
    name, out = sys.argv[1], sys.argv[2]
    T = build(name).astype(np.int64)
    N = len(T)
    assert (T[0] == np.arange(N)).all() and (T[:, 0] == np.arange(N)).all()
    with open(out, 'wb') as f:
        np.array([N], dtype=np.int32).tofile(f)
        T.astype(np.uint16).tofile(f)
    print(name, 'N =', N, 'written', out)

#!/usr/bin/env python3
"""c3 (squad r2_d14D8): coordinate-based voltages on H(q) + 2 point-line matchings, cyclic Z_m.

Library use:  from mk_c3 import build_edges ; E = build_edges(q, m, seed, hexmode, kappa, phimode)
CLI:          python3 mk_c3.py q m seed hexmode kappa phimode out
  hexmode: zero | rand | proj
           proj: h(p,l) = kappa(t_l(p)), t_l(p) in PG(1,q) = projective parameter of p on l
                 (basis LP[l][0], LP[l][1]: p = alpha*u + beta*v, t = beta/alpha, infinity = q)
  kappa  : (proj only) sing = Singer index of t (PG(1,q) = GF(q^2)^*/GF(q)^* = Z_{q+1}), mod m
           rand = random injective map PG(1,q) -> Z_m, lin = t mod m
  phimode: rand   two uniform random matchings, uniform random voltages
           ratio  mk_ratio.py colour matchings (colour = ratio of two random linear forms), voltage = colour + off
           rsing  two uniform random matchings, voltage(p) = Singer index of the ratio colour of p, mod m
Base file: 'N N m' then 'p l v' per edge; hexagon flags first (liftdiag needs this order).
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges


def inv_table(q):
    return np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)


def _primes(n):
    ps, d = [], 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ps.append(n)
    return ps


def singer_index(q):
    """t_to_idx[t] = i where t = projective parameter of w^i (w primitive in GF(q^2)), t in 0..q (q = infinity)."""
    n = next(a for a in range(2, q) if pow(a, (q - 1) // 2, q) == q - 1)  # non-residue, GF(q^2) = GF(q)[x]/(x^2-n)

    def mul(u, v):
        a, b = u
        c, d = v
        return ((a * c + n * b * d) % q, (a * d + b * c) % q)

    def power(u, e):
        r, b = (1, 0), u
        while e:
            if e & 1:
                r = mul(r, b)
            b = mul(b, b)
            e >>= 1
        return r

    order = q * q - 1
    w = None
    for a in range(q):
        for b in range(q):
            if (a, b) != (0, 0) and power((a, b), order) == (1, 0) and all(
                    power((a, b), order // p) != (1, 0) for p in _primes(order)):
                w = (a, b)
                break
        if w is not None:
            break
    idx_to_t, cur = [], (1, 0)
    for _ in range(q + 1):
        a, b = cur
        idx_to_t.append(q if a == 0 else (b * pow(a, q - 2, q)) % q)
        cur = mul(cur, w)
    assert sorted(idx_to_t) == list(range(q + 1))
    t_to_idx = np.zeros(q + 1, dtype=np.int64)
    for i, t in enumerate(idx_to_t):
        t_to_idx[t] = i
    return t_to_idx


def proj_params(q, X, LP):
    """T[l, k] in 0..q: projective parameter (w.r.t. basis LP[l,0], LP[l,1]) of the point LP[l,k] on line l."""
    L = LP.shape[0]
    U, V = X[LP[:, 0]], X[LP[:, 1]]
    pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
    det = np.stack([(U[:, i] * V[:, j] - U[:, j] * V[:, i]) % q for i, j in pairs], axis=1)
    piv = np.argmax(det != 0, axis=1)
    ar = np.arange(L)
    D = det[ar, piv]
    assert (D != 0).all()
    I = np.array([i for i, _ in pairs])[piv]
    J = np.array([j for _, j in pairs])[piv]
    inv = inv_table(q)
    dinv, ainv_full = inv[D], inv
    T = np.zeros(LP.shape, dtype=np.int64)
    for k in range(q + 1):
        P = X[LP[:, k]]
        Pi, Pj = P[ar, I], P[ar, J]
        Ui, Uj, Vi, Vj = U[ar, I], U[ar, J], V[ar, I], V[ar, J]
        alpha = ((Pi * Vj - Pj * Vi) % q) * dinv % q
        beta = ((Ui * Pj - Uj * Pi) % q) * dinv % q
        # verify P = alpha U + beta V on all coordinates
        assert (((alpha[:, None] * U + beta[:, None] * V) - P) % q == 0).all(), 'point not on line'
        t = (beta * ainv_full[alpha]) % q
        T[:, k] = np.where(alpha == 0, q, t)
    return T


def ratio(num, den, q, inv):
    num %= q
    den %= q
    r = (num * inv[den]) % q
    r = np.where(den == 0, q, r)
    return np.where((num == 0) & (den == 0), -1, r)


def dedup(E, m, rng):
    """No two base edges may share (point, line, voltage): a repeated triple is a double edge in the lift.
    Later duplicates (matching edges only, the hexagon flags come first) get a fresh uniform voltage."""
    E = E.copy()
    seen = set()
    for i in range(len(E)):
        p, l, v = int(E[i, 0]), int(E[i, 1]), int(E[i, 2]) % m
        while (p, l, v) in seen:
            v = int(rng.integers(0, m))
        seen.add((p, l, v))
        E[i, 2] = v
    return E


def build_edges(q, m, seed, hexmode='rand', kappa='rand', phimode='rand', hexrep=None):
    N, LP, PL, coord = load(q)
    X = coord.astype(np.int64)
    rng = np.random.default_rng(seed)
    L, Q1 = LP.shape
    if hexmode == 'zero':
        H = np.zeros((L, Q1), dtype=np.int64)
    elif hexmode == 'rand':
        H = rng.integers(0, m, (L, Q1))
    elif hexmode == 'proj':
        T = proj_params(q, X, LP)
        if kappa == 'sing':
            H = singer_index(q)[T] % m
        elif kappa == 'rand':
            assert m >= q + 1
            H = rng.choice(m, q + 1, replace=False)[T]
        elif kappa == 'lin':
            H = T % m
        else:
            raise ValueError(kappa)
    else:
        raise ValueError(hexmode)
    E = [hex_edges(LP, H)]
    inv = inv_table(q)
    if phimode == 'rand':
        for _ in range(2):
            E.append(np.stack([np.arange(N), rng.permutation(N), rng.integers(0, m, N)], axis=1))
    elif phimode in ('ratio', 'rsing'):
        A = X[LP[:, 0]]
        B = X[LP[:, 1]]
        pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
        PLK = np.stack([(A[:, i] * B[:, j] - A[:, j] * B[:, i]) % q for i, j in pairs], axis=1)
        sing = singer_index(q) if phimode == 'rsing' else None
        for _ in range(2):
            L1, L2 = rng.integers(0, q, 7), rng.integers(0, q, 7)
            cp = ratio(X @ L1, X @ L2, q, inv)
            G1, G2 = rng.integers(0, q, len(pairs)), rng.integers(0, q, len(pairs))
            cl = ratio(PLK @ G1, PLK @ G2, q, inv)
            if phimode == 'ratio':
                M = np.full(N, -1)
                leftP, freeL = [], []
                for c in range(-1, q + 1):
                    lc = list(rng.permutation(np.flatnonzero(cl == c)))
                    pc = list(rng.permutation(np.flatnonzero(cp == c)))
                    k = min(len(lc), len(pc))
                    M[pc[:k]] = lc[:k]
                    leftP += pc[k:]
                    freeL += lc[k:]
                freeL = rng.permutation(np.array(freeL, dtype=np.int64))
                M[np.array(leftP, dtype=np.int64)] = freeL
                off = int(rng.integers(0, m))
                psi = np.where(cp < 0, rng.integers(0, q + 1, N), cp) + off
            else:
                M = rng.permutation(N)
                col = np.where(cp < 0, rng.integers(0, q + 1, N), cp)
                psi = sing[col] + int(rng.integers(0, m))
            E.append(np.stack([np.arange(N), M, psi % m], axis=1))
    else:
        raise ValueError(phimode)
    return N, dedup(np.concatenate(E), m, rng)


if __name__ == '__main__':
    q, m, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    hexmode, kappa, phimode, out = sys.argv[4:8]
    N, E = build_edges(q, m, seed, hexmode, kappa, phimode)
    write_base(out, N, m, E)
    print(f'wrote {out}: N {N} m {m} edges {len(E)}')


def build_lev(q, k, seed, hexsub='proj', colour='ratio', phi2='same', L=5):
    """Level family (opus/mk_lev.py style) with coordinate sub-voltages. Lift group Z_L x Z_k = Z_{L k} (gcd(L,k)=1).
    Hexagon flags: level 0, sub-voltage kappa(t_l(p)) (hexsub=proj, kappa = Singer index mod k) or random (rand) or 0.
    Extra edges: phi(p) gets (level 1, sub a(p)) and (level 2, sub b(p)); phi = colour-matching (colour='ratio': the
    ratio colour c1 of p matched to the line colour of the same class) or random (colour='rand').
    a(p) = singer(c1(p)) mod k, b(p) = singer(c2(p)) mod k, c2 = second ratio colour (or same as c1 if phi2='same')."""
    from math import gcd
    assert gcd(L, k) == 1
    m = L * k
    T = np.zeros((L, k), dtype=np.int64)
    for x in range(m):
        T[x % L, x % k] = x
    N, LP, PL, coord = load(q)
    X = coord.astype(np.int64)
    rng = np.random.default_rng(seed)
    inv = inv_table(q)
    Lh, Q1 = LP.shape
    if hexsub == 'proj':
        Tp = proj_params(q, X, LP)
        H = singer_index(q)[Tp] % k
    elif hexsub == 'rand':
        H = rng.integers(0, k, (Lh, Q1))
    else:
        H = np.zeros((Lh, Q1), dtype=np.int64)
    E = [hex_edges(LP, T[0, H])]
    A = X[LP[:, 0]]
    B = X[LP[:, 1]]
    pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
    PLK = np.stack([(A[:, i] * B[:, j] - A[:, j] * B[:, i]) % q for i, j in pairs], axis=1)
    sing = singer_index(q)

    def colours():
        L1, L2 = rng.integers(0, q, 7), rng.integers(0, q, 7)
        cp = ratio(X @ L1, X @ L2, q, inv)
        cp = np.where(cp < 0, rng.integers(0, q + 1, N), cp)
        G1, G2 = rng.integers(0, q, len(pairs)), rng.integers(0, q, len(pairs))
        cl = ratio(PLK @ G1, PLK @ G2, q, inv)
        cl = np.where(cl < 0, rng.integers(0, q + 1, N), cl)
        return cp, cl

    cp, cl = colours()
    if colour == 'ratio':
        M = np.full(N, -1)
        leftP, freeL = [], []
        for c in range(0, q + 1):
            lc = list(rng.permutation(np.flatnonzero(cl == c)))
            pc = list(rng.permutation(np.flatnonzero(cp == c)))
            kk = min(len(lc), len(pc))
            M[pc[:kk]] = lc[:kk]
            leftP += pc[kk:]
            freeL += lc[kk:]
        freeL = rng.permutation(np.array(freeL, dtype=np.int64))
        M[np.array(leftP, dtype=np.int64)] = freeL
    else:
        M = rng.permutation(N)
    if phi2 == 'same':
        cp2 = cp
    else:
        cp2, _ = colours()
    a = sing[cp] % k
    b = sing[cp2] % k
    E.append(np.stack([np.arange(N), M, T[1 % L, a]], axis=1))
    E.append(np.stack([np.arange(N), M, T[2 % L, b]], axis=1))
    return m, N, np.concatenate(E)

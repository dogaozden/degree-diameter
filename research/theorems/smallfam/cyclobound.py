"""Cyclotomic action-order bound: a rigorous upper bound on |G| for Haar graphs of G = Z_p x|_r Z_k (p prime).

Let o = ord_p(r) (o | k, o | p-1).  Normal form (frob_scan.py): S = {(0,0), (0,j1), (1,j2), (a3,j3), ...} with
o not dividing j1.  r is a primitive o-th root of unity in F_p, so P(r) depends only on P mod Phi_o.  Put
    U = Z[zeta_o]^F x| Z_k,   (P; J)(Q; L) = (P + zeta^J Q; J + L),   F = Delta - 2,
    u_0 = e, u_1 = (0; j1), u_i = (eps_{i-1}; j_i) for i >= 2.
phi(P; J) = (sum_f P_f(r) a_{f+2}, J) (a_2 = 1) is a homomorphism U -> G with phi(u_i) = s_i, and maps the ball of
radius D around (e,A) (resp. (e,B)) of the infinite Haar graph H(U, {u_i}) ONTO the ball in H(G, S).  So
    N = |G| <= B(k, o, j) := min over start side and target side of the ball counts in H(U),
for every a3, a4, ... and every p with ord_p(r) = o.  B(k, o) = max over admissible j (j1 not = 0 mod o, the j_i
generating Z_k; j up to multiplication by units of Z_k, which is the Galois action zeta -> zeta^u).
If N > B(k, o) the group has no Haar graph of diameter <= D at all.
Usage:
  python3 cyclobound.py bound DELTA D k o                 one value, with the maximizing j
  python3 cyclobound.py scan DELTA D FILE [FILE ...]       apply to every group line "p k r o N ..." of frob_scan output
"""
import itertools
import sys
from math import gcd

import numpy as np


def cyclotomic(n, _cache={}):
    """Integer coefficients of Phi_n, lowest degree first."""
    if n in _cache:
        return _cache[n]
    num = [-1] + [0] * (n - 1) + [1]                 # x^n - 1
    for d in range(1, n):
        if n % d == 0:
            den = cyclotomic(d)
            # exact division num / den
            out = [0] * (len(num) - len(den) + 1)
            rem = num[:]
            for i in range(len(out) - 1, -1, -1):
                c = rem[i + len(den) - 1] // den[-1]
                out[i] = c
                for t in range(len(den)):
                    rem[i + t] -= c * den[t]
            assert all(x == 0 for x in rem[:len(den) - 1])
            num = out
    _cache[n] = num
    return num


def zeta_powers(o):
    """M[t] = matrix of multiplication by zeta^t on Z[zeta_o] in the basis 1, zeta, ..., zeta^(phi-1) (column = image)."""
    phi = cyclotomic(o)
    f = len(phi) - 1
    C = np.zeros((f, f), dtype=np.int64)
    for i in range(f - 1):
        C[i + 1, i] = 1
    for i in range(f):
        C[i, f - 1] = -phi[i]
    M = [np.eye(f, dtype=np.int64)]
    for t in range(1, o):
        M.append(C @ M[-1])
    return M, f


def ball_bound(Delta, D, k, o, j):
    """min over (start side, target side) of the number of distinct vertices within D in H(U, {u_i})."""
    M, f = zeta_powers(o)
    F = Delta - 2
    width = F * f
    # generator i: (eps, j_i); eps = basis vector e_0 of formal part i-2
    eps = []
    for i in range(Delta):
        v = np.zeros(width, dtype=np.int64)
        if i >= 2:
            v[(i - 2) * f] = 1
        eps.append(v)

    def act(P, t):          # multiply each formal part by zeta^t; P is (n, width)
        t %= o
        if t == 0:
            return P.copy()
        out = np.empty_like(P)
        for fi in range(F):
            out[:, fi * f:(fi + 1) * f] = P[:, fi * f:(fi + 1) * f] @ M[t].T
        return out

    best = None
    for start in (0, 1):                       # 0 = start at (e,A), 1 = (e,B)
        P = np.zeros((1, width), dtype=np.int64)
        J = np.zeros(1, dtype=np.int64)
        side = start
        seen = [set(), set()]
        seen[side].add(P[0].tobytes() + J[0:1].tobytes())
        for d in range(1, D + 1):
            newP, newJ = [], []
            for i in range(Delta):
                if side == 0:     # (g,A) ~ (u_i g, B): u_i (P;J) = (eps_i + zeta^{j_i} P; j_i + J)
                    Q = act(P, j[i]) + eps[i]
                    L = (J + j[i]) % k
                else:             # (g,B) ~ (u_i^-1 g, A): u_i^-1 (P;J) = (zeta^{-j_i}(P - eps_i); J - j_i)
                    Q = act(P - eps[i], -j[i])
                    L = (J - j[i]) % k
                newP.append(Q)
                newJ.append(L)
            Q = np.concatenate(newP)
            L = np.concatenate(newJ)
            nside = 1 - side
            keepP, keepJ = [], []
            for row, jj in zip(Q, L):
                key = row.tobytes() + np.int64(jj).tobytes()
                if key not in seen[nside]:
                    seen[nside].add(key)
                    keepP.append(row)
                    keepJ.append(jj)
            if keepP:
                P = np.array(keepP)
                J = np.array(keepJ, dtype=np.int64)
            else:
                P = np.zeros((0, width), dtype=np.int64)
                J = np.zeros(0, dtype=np.int64)
            side = nside
        if FIBER:
            # every fibre J of Z_k must hold p distinct elements: p <= min_J count, so N <= k * min_J count
            for sd in (0, 1):
                cnt = {}
                for key in seen[sd]:
                    jj = int(np.frombuffer(key[-8:], dtype=np.int64)[0])
                    cnt[jj] = cnt.get(jj, 0) + 1
                c = k * min(cnt.get(x, 0) for x in range(k))
                best = c if best is None else min(best, c)
        else:
            c = min(len(seen[0]), len(seen[1]))
            best = c if best is None else min(best, c)
    return best


FIBER = False


def admissible_js(Delta, k, o):
    seen = set()
    units = [u for u in range(1, k + 1) if gcd(u, k) == 1] if k > 1 else [1]
    for js in itertools.product(range(k), repeat=Delta - 1):
        j = (0,) + js
        if j[1] % o == 0:
            continue
        g = 0
        for x in js:
            g = gcd(g, x)
        if gcd(g, k) != 1:
            continue
        cls = min(tuple((u * x) % k for x in j) for u in units)
        if cls in seen:
            continue
        seen.add(cls)
        yield j


def bound(Delta, D, k, o, _cache={}):
    key = (Delta, D, k, o)
    if key not in _cache:
        b, bj = -1, None
        for j in admissible_js(Delta, k, o):
            v = ball_bound(Delta, D, k, o, j)
            if v > b:
                b, bj = v, j
        _cache[key] = (b, bj)
    return _cache[key]


def main():
    global FIBER
    if '--fiber' in sys.argv:
        FIBER = True
        sys.argv.remove('--fiber')
    if sys.argv[1] == 'bound':
        Delta, D, k, o = map(int, sys.argv[2:6])
        print(Delta, D, k, o, *bound(Delta, D, k, o))
        return
    Delta, D = int(sys.argv[2]), int(sys.argv[3])
    for fn in sys.argv[4:]:
        for line in open(fn):
            f = line.split()
            if len(f) < 6 or not f[0].isdigit():
                continue
            p, k, r, o, N = map(int, f[:5])
            sol = [x for x in f if x.startswith('solutions=')]
            nsol = int(sol[0].split('=')[1]) if sol else -1
            b, bj = bound(Delta, D, k, o)
            print(f'{p} {k} {r} {o} {N} index={(p - 1) // o} solutions={nsol} bound={b} '
                  f'{"EXCLUDED" if N > b else "open"} j={bj}', flush=True)


if __name__ == "__main__" and sys.argv[1] != "generic":
    main()


def ball_bound_generic(Delta, D, o, j):
    """As ball_bound, but the Z_k part is replaced by the signed generator counts n in Z^(Delta-1) (no wrap-around), so
    the value bounds N for every k (action exponent <n, j> mod o)."""
    M, f = zeta_powers(o)
    F = Delta - 2
    width = F * f
    eps = []
    for i in range(Delta):
        v = np.zeros(width, dtype=np.int64)
        if i >= 2:
            v[(i - 2) * f] = 1
        eps.append(v)
    jv = np.array(j[1:], dtype=np.int64)

    def act_rows(P, t):     # row-wise multiplication by zeta^t[row]
        out = np.empty_like(P)
        for tt in np.unique(t):
            sel = t == tt
            for fi in range(F):
                out[sel, fi * f:(fi + 1) * f] = P[sel, fi * f:(fi + 1) * f] @ M[int(tt)].T
        return out

    best = None
    for start in (0, 1):
        P = np.zeros((1, width), dtype=np.int64)
        Nn = np.zeros((1, Delta - 1), dtype=np.int64)
        side = start
        seen = [set(), set()]
        seen[side].add(P[0].tobytes() + Nn[0].tobytes())
        for d in range(1, D + 1):
            newP, newN = [], []
            for i in range(Delta):
                ei = np.zeros(Delta - 1, dtype=np.int64)
                if i >= 1:
                    ei[i - 1] = 1
                if side == 0:   # u_i g: eps_i + zeta^{j_i} P
                    Q = act_rows(P, np.full(len(P), j[i] % o)) + eps[i]
                    L = Nn + ei
                else:           # u_i^-1 g: zeta^{-j_i} (P - eps_i)
                    Q = act_rows(P - eps[i], np.full(len(P), (-j[i]) % o))
                    L = Nn - ei
                newP.append(Q)
                newN.append(L)
            Q = np.concatenate(newP)
            L = np.concatenate(newN)
            nside = 1 - side
            keep = []
            for idx in range(len(Q)):
                key = Q[idx].tobytes() + L[idx].tobytes()
                if key not in seen[nside]:
                    seen[nside].add(key)
                    keep.append(idx)
            P, Nn = Q[keep], L[keep]
            side = nside
        c = min(len(seen[0]), len(seen[1]))
        best = c if best is None else min(best, c)
    return best


def generic_table(Delta, D, omax):
    print(f'# Delta={Delta} D={D}: B_gen(o) = max over j mod o (j1 not 0 mod o) of the k-independent ball bound')
    for o in range(2, omax + 1):
        b, bj = -1, None
        seen = set()
        units = [u for u in range(1, o) if gcd(u, o) == 1]
        for js in itertools.product(range(o), repeat=Delta - 1):
            j = (0,) + js
            if j[1] % o == 0:
                continue
            cls = min(tuple((u * x) % o for x in j) for u in units)
            if cls in seen:
                continue
            seen.add(cls)
            v = ball_bound_generic(Delta, D, o, j)
            if v > b:
                b, bj = v, j
        print(f'{o:3d} phi={len(cyclotomic(o)) - 1:3d}  B_gen={b:8d}  j={bj}', flush=True)


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'generic':
    generic_table(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))

#!/usr/bin/env python3
"""c3 referee check of SMALL_DEGREE_FAMILIES.md section 2.3 and smallfam/cyclobound.py.

Pure-Python re-implementation, independent of cyclobound's companion matrices and BFS:
  - Z[zeta_o] = Z[x]/Phi_o, with Phi_o taken from numerical roots (rounded), reduction by hand;
  - the universal group U = Z[zeta]^(Delta-2) x| Z_k with the product (P;J)(Q;L) = (P + zeta^J Q; J+L) and the
    generic inverse (-zeta^-J P; -J), generators u_0 = e, u_1 = (0;j1), u_i = (eps_{i-2}; j_i);
  - the Haar graph H(G,S) on G = Z_p x|_r Z_k with its own multiplication, S = {s_i = (a_i, j_i)}, s_0 = (0,0),
    s_1 = (0,j1), a_2..a_{Delta-1} random (NOT normalised to a_2 = 1);
  - psi(P;J) = (sum_f ev_r(P_f) a_{f+2}, J) with ev_r: zeta -> r.
Checks: (1) psi is a homomorphism and psi(u_i) = s_i; (2) psi(ball_U(start)) = ball_G(start) exactly, per side and
fibre; (3) cyclobound.ball_bound (FIBER on/off) equals the value computed here; (4) soundness: for connected H(G,S)
with diameter D0, the bound at D = D0 is >= N; (5) admissible_js enumerates each unit-orbit of admissible j once and
ball_bound is invariant under j -> u j.
"""
import itertools
import random
import sys
from math import gcd

import numpy as np

sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/smallfam')
import cyclobound as cb  # read-only use of the code under review


def phi_numeric(o):
    roots = [np.exp(2j * np.pi * a / o) for a in range(1, o + 1) if gcd(a, o) == 1]
    c = np.poly(roots)
    assert max(abs(c.imag)) < 1e-9
    return [int(round(x.real)) for x in c[::-1]]          # lowest degree first, monic


class Ring:
    def __init__(self, o):
        self.o = o
        self.Phi = phi_numeric(o)
        self.n = len(self.Phi) - 1

    def mulx(self, v):                                    # x * v mod Phi_o
        top = v[-1]
        new = [0] + list(v[:-1])
        for i in range(self.n):
            new[i] -= top * self.Phi[i]
        return tuple(new)

    def mulz(self, v, t):                                 # zeta^t * v
        for _ in range(t % self.o):
            v = self.mulx(v)
        return v

    def add(self, u, v):
        return tuple(a + b for a, b in zip(u, v))

    def neg(self, u):
        return tuple(-a for a in u)

    def zero(self):
        return tuple([0] * self.n)

    def one(self):
        return tuple([1] + [0] * (self.n - 1))


class Univ:
    def __init__(self, Delta, k, o, j):
        self.Delta, self.k, self.o, self.j = Delta, k, o, j
        self.R = Ring(o)
        self.F = Delta - 2

    def mul(self, x, y):
        (P, J), (Q, L) = x, y
        R = self.R
        return (tuple(R.add(P[f], R.mulz(Q[f], J)) for f in range(self.F)), (J + L) % self.k)

    def inv(self, x):
        P, J = x
        R = self.R
        return (tuple(R.neg(R.mulz(P[f], (-J) % self.o)) for f in range(self.F)), (-J) % self.k)

    def gen(self, i):
        Pl = [self.R.zero() for _ in range(self.F)]
        if i >= 2:
            Pl[i - 2] = self.R.one()
        return (tuple(Pl), self.j[i] % self.k)

    def e(self):
        return (tuple(self.R.zero() for _ in range(self.F)), 0)


def u_ball(U, D, start):
    """vertices (g, side) of H(U, {u_i}) within distance D of (e, start): returns [set_side0, set_side1] of (P;J)."""
    gens = [U.gen(i) for i in range(U.Delta)]
    ginv = [U.inv(g) for g in gens]
    e = U.e()
    vis = [set(), set()]
    vis[start].add(e)
    frontier, side = [e], start
    for _ in range(D):
        nside = 1 - side
        nxt = []
        for g in frontier:
            for i in range(U.Delta):
                h = U.mul(gens[i], g) if side == 0 else U.mul(ginv[i], g)   # (g,A)~(u g,B); (g,B)~(u^-1 g,A)
                if h not in vis[nside]:
                    vis[nside].add(h)
                    nxt.append(h)
        frontier, side = nxt, nside
    return vis


class Grp:
    def __init__(self, p, k, r):
        self.p, self.k, self.r = p, k, r
        self.rp = [pow(r, j, p) for j in range(k)]

    def mul(self, x, y):
        (a, j), (b, l) = x, y
        return ((a + self.rp[j] * b) % self.p, (j + l) % self.k)

    def inv(self, x):
        a, j = x
        jj = (-j) % self.k
        return ((-self.rp[jj] * a) % self.p, jj)


def g_ball(G, S, D, start):
    Sinv = [G.inv(s) for s in S]
    vis = [set(), set()]
    e = (0, 0)
    vis[start].add(e)
    frontier, side = [e], start
    for _ in range(D):
        nside = 1 - side
        nxt = []
        for g in frontier:
            for h in ([G.mul(s, g) for s in S] if side == 0 else [G.mul(t, g) for t in Sinv]):
                if h not in vis[nside]:
                    vis[nside].add(h)
                    nxt.append(h)
        frontier, side = nxt, nside
    return vis


def haar_diameter(G, S):
    """exact diameter of H(G,S) by BFS from all 2|G| vertices; None if disconnected."""
    Sinv = [G.inv(s) for s in S]
    verts = [((a, j), side) for a in range(G.p) for j in range(G.k) for side in (0, 1)]
    best = 0
    for src in verts:
        dist = {src: 0}
        q = [src]
        for v in q:
            g, side = v
            nbrs = [(G.mul(s, g), 1) for s in S] if side == 0 else [(G.mul(t, g), 0) for t in Sinv]
            for w in nbrs:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    q.append(w)
        if len(dist) < len(verts):
            return None
        best = max(best, max(dist.values()))
    return best


def psi(R_phi_ev, p, r, avals, x):
    P, J = x
    a = 0
    for f, Pf in enumerate(P):
        ev = sum(c * pow(r, t, p) for t, c in enumerate(Pf)) % p
        a = (a + ev * avals[f]) % p
    return (a, J)


def my_bounds(U, Ub, k):
    """fibre value min_{start,side,J} k*count and non-fibre value min_{start,side} |ball|, from Ub[start][side]."""
    fib, nofib = None, None
    for start in (0, 1):
        for side in (0, 1):
            cnt = {}
            for (P, J) in Ub[start][side]:
                cnt[J] = cnt.get(J, 0) + 1
            c = k * min(cnt.get(x, 0) for x in range(k))
            fib = c if fib is None else min(fib, c)
            c2 = len(Ub[start][side])
            nofib = c2 if nofib is None else min(nofib, c2)
    return fib, nofib


def run_case(p, k, r, o, Delta, D, rng, ntrial):
    assert pow(r, o, p) == 1 and all(pow(r, t, p) != 1 for t in range(1, o)) and k % o == 0
    G = Grp(p, k, r)
    Phi = phi_numeric(o)
    assert sum(c * pow(r, t, p) for t, c in enumerate(Phi)) % p == 0, "Phi_o(r) != 0 mod p"
    out = []
    for trial in range(ntrial):
        j1 = rng.choice([x for x in range(1, k) if x % o])
        js = [rng.randrange(k) for _ in range(Delta - 2)]
        j = (0, j1, *js)
        avals = [rng.randrange(p) for _ in range(Delta - 2)]        # a_2, ..., a_{Delta-1}, unnormalised
        S = [(0, 0), (0, j1)] + [(avals[f], js[f]) for f in range(Delta - 2)]
        if len(set(S)) != Delta:
            continue
        U = Univ(Delta, k, o, j)
        # (1) homomorphism and generators
        for i in range(Delta):
            assert psi(None, p, r, avals, U.gen(i)) == S[i], ("psi(u_i) != s_i", i)
        for _ in range(60):
            x = (tuple(U.R.zero() if rng.random() < .3 else tuple(rng.randrange(-3, 4) for _ in range(U.R.n))
                       for _ in range(U.F)), rng.randrange(k))
            y = (tuple(tuple(rng.randrange(-3, 4) for _ in range(U.R.n)) for _ in range(U.F)), rng.randrange(k))
            assert U.mul(x, U.inv(x)) == U.e()
            lhs = psi(None, p, r, avals, U.mul(x, y))
            rhs = G.mul(psi(None, p, r, avals, x), psi(None, p, r, avals, y))
            assert lhs == rhs, "psi not a homomorphism"
        # (2) image of the universal ball equals the group ball, per start, side, fibre
        Ub = [u_ball(U, D, s) for s in (0, 1)]
        for s in (0, 1):
            Gb = g_ball(G, S, D, s)
            for side in (0, 1):
                img = {psi(None, p, r, avals, x) for x in Ub[s][side]}
                assert img == Gb[side], ("image != ball", p, k, r, o, j, S, s, side)
        # (3) code agreement
        cb.FIBER = True
        code_fib = cb.ball_bound(Delta, D, k, o, j)
        cb.FIBER = False
        code_nofib = cb.ball_bound(Delta, D, k, o, j)
        my_fib, my_nofib = my_bounds(U, Ub, k)
        assert code_fib == my_fib, ("fibre value mismatch", code_fib, my_fib, j)
        assert code_nofib == my_nofib, ("nofibre value mismatch", code_nofib, my_nofib, j)
        # (4) soundness at the true diameter
        D0 = haar_diameter(G, S)
        if D0 is not None:
            N = p * k
            cb.FIBER = True
            code_at_D0 = cb.ball_bound(Delta, D0, k, o, j)
            assert code_at_D0 >= N, ("UNSOUND", p, k, r, o, j, S, D0, code_at_D0)
            out.append((S, j, D0, code_at_D0, N))
        cb.FIBER = False
        out.append(('ok', (p, k, r, o), j, D, my_fib, my_nofib))
    return out


def check_admissible(Delta, k, o):
    units = [u for u in range(1, k + 1) if gcd(u, k) == 1] if k > 1 else [1]
    classes = set()
    for js in itertools.product(range(k), repeat=Delta - 1):
        j = (0,) + js
        if j[1] % o == 0:
            continue
        g = 0
        for x in js:
            g = gcd(g, x)
        if gcd(g, k) != 1:
            continue
        classes.add(min(tuple((u * x) % k for x in j) for u in units))
    yielded = list(cb.admissible_js(Delta, k, o))
    ycls = [min(tuple((u * x) % k for x in j) for u in units) for j in yielded]
    assert len(ycls) == len(set(ycls)), "admissible_js yields a unit-orbit twice"
    assert set(ycls) == classes, "admissible_js misses or adds a class"
    return len(classes)


def main():
    rng = random.Random(7)
    groups = [(7, 6, 2, 3), (7, 12, 2, 3), (7, 6, 6, 2), (13, 12, 5, 4), (11, 10, 2, 10), (11, 5, 3, 5),
              (19, 9, 4, 9)]
    print('== (1)-(4): images, code agreement, soundness ==')
    nconn = 0
    for (p, k, r, o) in groups:
        for Delta, D in ((3, 4), (3, 5), (4, 4)):
            res = run_case(p, k, r, o, Delta, D, rng, ntrial=3)
            for row in res:
                if row[0] == 'ok':
                    continue
                nconn += 1
            print(f'Z{p} x|_{r} Z{k} (o={o}) Delta={Delta} D={D}: image=ball, code=mine: ok; '
                  f'connected cases with diameter: {sum(1 for x in res if x[0] != "ok")}')
    print(f'soundness checked on {nconn} connected Haar graphs (code bound at diameter >= N, no UNSOUND assertion)')
    print('== (5) admissible classes and unit invariance ==')
    total = 0
    for k in (4, 6, 8, 9, 10, 12):
        for o in range(2, k + 1):
            if k % o == 0:
                for Delta in (3, 4):
                    total += check_admissible(Delta, k, o)
    print(f'admissible_js: unit-orbit classes match brute force for all tested (k,o,Delta); total classes {total}')
    for (k, o, Delta, D) in ((6, 3, 3, 5), (12, 4, 3, 5), (12, 6, 3, 5)):
        for js in list(cb.admissible_js(Delta, k, o))[:6]:
            cb.FIBER = True
            base = cb.ball_bound(Delta, D, k, o, js)
            for u in range(1, k + 1):
                if gcd(u, k) != 1:
                    continue
                uj = tuple((u * x) % k for x in js)
                assert cb.ball_bound(Delta, D, k, o, uj) == base, ("unit invariance fails", js, u)
            cb.FIBER = False
    print('ball_bound (fibre) invariant under j -> u j for the tested admissible j')


if __name__ == '__main__':
    main()

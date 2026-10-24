"""Metacyclic Haar graphs: parse every saved solution, check it, and put it in normal form.

G = Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l)  (the Loz-Siran convention used by haar_gen3, lift.c, build.py).
Haar graph H(G,S): (g,A) ~ (s g, B), s in S.  Right multiplication by G is transitive on each side, so
  D even: every (g,B) within D-1 of (e,A);   D odd: every (g,A) within D-1 of (e,A) and every (g,B) within D-1 of (e,B).

Usage: python3 meta.py          (parse + check all files in sols_meta/ and the D=5/D=7 folders; prints a table)
"""
import glob
import os
import re
import sys
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def ordmod(r, m):
    if m == 1:
        return 1
    x, t = r % m, 1
    while x != 1 % m:
        x = x * r % m
        t += 1
        if t > m:
            return None
    return t


class Meta:
    def __init__(self, m, k, r):
        assert pow(r, k, m) == 1 % m, (m, k, r)
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        self.rp = [pow(r, j, m) for j in range(k)]

    def idx(self, a, j):
        return (a % self.m) * self.k + (j % self.k)

    def el(self, i):
        return divmod(i, self.k)

    def mul(self, x, y):
        (a, j), (b, l) = x, y
        return ((a + self.rp[j % self.k] * b) % self.m, (j + l) % self.k)

    def inv(self, x):
        a, j = x
        jj = (-j) % self.k
        return ((-self.rp[jj] * a) % self.m, jj)

    def left_perm(self, s):
        """array P with P[idx(g)] = idx(s g)"""
        a, j = s
        A = np.arange(self.m)[:, None]
        L = np.arange(self.k)[None, :]
        na = (a + self.rp[j % self.k] * A) % self.m
        nl = (j + L) % self.k
        return (na * self.k + nl).reshape(-1)


def haar_ecc(G, S, D):
    """returns (ok, uncovered_count, eccA, eccB) following the conditions in the module docstring"""
    N = G.N
    P = [G.left_perm(s) for s in S]                       # (g,A) -> (s g, B)
    Pinv = [G.left_perm(G.inv(s)) for s in S]           # (h,B) -> (s^-1 h, A)

    def bfs(startB):
        # returns distance arrays dA, dB (int, -1 = unreached)
        dA = -np.ones(N, dtype=np.int32)
        dB = -np.ones(N, dtype=np.int32)
        e = G.idx(0, 0)
        if startB:
            dB[e] = 0
            front, side = np.array([e]), 'B'
        else:
            dA[e] = 0
            front, side = np.array([e]), 'A'
        d = 0
        while len(front):
            d += 1
            if side == 'A':
                nb = np.unique(np.concatenate([p[front] for p in P]))
                nb = nb[dB[nb] < 0]
                dB[nb] = d
                front, side = nb, 'B'
            else:
                nb = np.unique(np.concatenate([q_[front] for q_ in Pinv]))
                nb = nb[dA[nb] < 0]
                dA[nb] = d
                front, side = nb, 'A'
        return dA, dB

    dA, dB = bfs(False)
    eA = max(dA.max(), dB.max()) if (dA >= 0).all() and (dB >= 0).all() else 10**9
    if D % 2 == 0:
        unc = int(((dB < 0) | (dB > D - 1)).sum())
        return unc == 0, unc, eA, None
    dA2, dB2 = bfs(True)
    eB = max(dA2.max(), dB2.max()) if (dA2 >= 0).all() and (dB2 >= 0).all() else 10**9
    unc = int(((dA < 0) | (dA > D - 1)).sum()) + int(((dB2 < 0) | (dB2 > D - 1)).sum())
    return unc == 0, unc, eA, eB


def parse(path):
    """-> dict(Delta, D, m, k, r, S=[(a,j)...], file) or None"""
    txt = open(path).read().strip().splitlines()
    h = txt[0].split()
    base = os.path.basename(path)
    # haar_gen3 format: "Delta D meta m k r n 1 N .."
    if len(h) >= 6 and h[2] == 'meta':
        Delta, D, m, k, r = int(h[0]), int(h[1]), int(h[3]), int(h[4]), int(h[5])
        n = int(h[h.index('n') + 1]) if 'n' in h else 1
        if n != 1:
            return None
        S = []
        for line in txt[1:]:
            mm = re.search(r'a=(\d+),j=(\d+)', line)
            if mm:
                S.append((int(mm.group(1)), int(mm.group(2))))
        return dict(Delta=Delta, D=D, m=m, k=k, r=r, S=S, file=base)
    # lift.c format converted from haar_gen3
    if txt[0].startswith('#') or txt[0].startswith('lift'):
        lines = [l for l in txt if not l.startswith('#')]
        hh = lines[0].split()
        D, Delta = int(hh[hh.index('D') + 1]), int(hh[hh.index('Delta') + 1])
        g = lines[1].split()
        if g[1] != 'meta' or len(g) != 5:
            return None
        m, k, r = int(g[2]), int(g[3]), int(g[4])
        S = []
        for l in lines[3:]:
            mm = re.search(r'=\s*(\d+),(\d+)', l)
            S.append((int(mm.group(1)), int(mm.group(2))))
        return dict(Delta=Delta, D=D, m=m, k=k, r=r, S=S, file=base)
    # research/d5 format: "Delta m k r" then "a j" lines, D = 5
    if len(h) == 4 and all(x.isdigit() for x in h):
        Delta, m, k, r = map(int, h)
        S = [tuple(map(int, l.split())) for l in txt[1:] if l.strip()]
        return dict(Delta=Delta, D=5, m=m, k=k, r=r, S=S, file=base)
    return None


def all_solutions():
    files = sorted(glob.glob(os.path.join(HERE, 'sols_meta', '*.txt')))
    files += sorted(glob.glob(os.path.join(ROOT, 'research', 'd5', 'sols', '*.txt')))
    files += sorted(glob.glob(os.path.join(ROOT, 'research', 'frontier', 'sols', '*meta*.txt')))
    out = []
    for f in files:
        try:
            s = parse(f)
        except Exception:
            s = None
        if s and len(s['S']) == s['Delta']:
            out.append(s)
    return out


if __name__ == '__main__':
    sols = all_solutions()
    print(f'{len(sols)} metacyclic Haar solutions parsed')
    print('Delta D | m k r ord_m(r) | N=mk  2N | valid uncovered | file')
    for s in sols:
        G = Meta(s['m'], s['k'], s['r'])
        ok, unc, eA, eB = haar_ecc(G, s['S'], s['D'])
        print(s['Delta'], s['D'], '|', s['m'], s['k'], s['r'], ordmod(s['r'], s['m']), '|', G.N, 2 * G.N, '|', ok, unc,
              '|', s['file'])

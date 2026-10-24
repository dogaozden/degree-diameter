"""c4 card: K-equivariant hop matchings and K-orbit labels for lifts of H(q) + 2 hops.

T = {diag(a0,a1,a2,1,1/a0,1/a1,1/a2) : a0 a1 a2 = 1} preserves H(q) (checked). For the full T no
T-equivariant bijection of points->lines exists at q=5 (orbit-stabilizer multiplicities differ), so the
hops are equivariant only under a subgroup K of T that admits one; K4 = 2-torsion of T was the largest.
Hop k at point p has voltage (t_k, c_k(K-orbit of p)) in Z_5 x Z_k.
"""
import collections
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402

LIFTW = os.path.join(HERE, 'liftw')


def inv(a, q):
    return pow(int(a), q - 2, q)


def _orbits(perms):
    n = len(perms[0])
    nK = len(perms)
    stab = [frozenset(t for t in range(nK) if perms[t][x] == x) for x in range(n)]
    oid = -np.ones(n, dtype=int)
    orbs = []
    for x in range(n):
        if oid[x] < 0:
            O = sorted(set(int(perms[t][x]) for t in range(nK)))
            for y in O:
                oid[y] = len(orbs)
            orbs.append(O)
    for O in orbs:
        assert len({stab[x] for x in O}) == 1
    return oid, orbs, stab


class Sym:
    def __init__(self, q, which='K4'):
        self.q = q
        H = gh.load(q)
        self.H = H
        N = self.N = H.N
        P = np.array(H.P) % q
        self.P = P

        def norm(v):
            for x in v:
                if x:
                    i = inv(x, q)
                    return tuple((y * i) % q for y in v)
            raise ValueError('zero vector')

        pt = {}
        for p in range(N):
            key = norm([int(x) for x in P[p]])
            assert key not in pt
            pt[key] = p
        T = []
        for a0 in range(1, q):
            for a1 in range(1, q):
                a2 = inv(a0 * a1 % q, q)
                T.append([a0, a1, a2, 1, inv(a0, q), inv(a1, q), inv(a2, q)])
        allp, alll = [], []
        for d in T:
            perm = np.array([pt[norm([(d[i] * int(P[p][i])) % q for i in range(7)])] for p in range(N)])
            assert len(set(perm.tolist())) == N
            allp.append(perm)
        lk = {frozenset(int(x) for x in H.lines[k]): k for k in range(N)}
        assert len(lk) == N
        for perm in allp:
            lp = np.array([lk[frozenset(int(perm[p]) for p in H.lines[k])] for k in range(N)])
            assert len(set(lp.tolist())) == N
            alll.append(lp)
        if which == 'T':
            K = list(range(len(T)))
        elif which == 'K4':
            K = [i for i, d in enumerate(T) if all((d[j] * d[j]) % q == 1 for j in range(3))]
        else:
            raise ValueError(which)
        self.K = K
        self.nK = len(K)
        self.pperm = [allp[i] for i in K]
        self.lperm = [alll[i] for i in K]
        self.porb, self.pO, self.pstab = _orbits(self.pperm)
        self.lorb, self.lO, self.lstab = _orbits(self.lperm)
        self.nporb = len(self.pO)
        self.flag_strs = ['%d %d 0 0\n' % (p, L) for (p, L) in gh.flags(H)]

    def stab_summary(self):
        cp = collections.Counter((len(O), tuple(sorted(self.pstab[O[0]]))) for O in self.pO)
        cl = collections.Counter((len(O), tuple(sorted(self.lstab[O[0]]))) for O in self.lO)
        return cp == cl, len(self.pO), len(self.lO)

    def matching(self, rng):
        """K-equivariant bijection s: points -> lines (s[p] = line index), random choice."""
        byS_p = collections.defaultdict(list)
        for i, O in enumerate(self.pO):
            byS_p[self.pstab[O[0]]].append(i)
        byS_l = collections.defaultdict(list)
        for j, O in enumerate(self.lO):
            byS_l[self.lstab[O[0]]].append(j)
        for S in set(byS_p) | set(byS_l):
            if len(byS_p.get(S, [])) != len(byS_l.get(S, [])):
                raise ValueError('stabilizer class mismatch: no equivariant bijection')
        s = -np.ones(self.N, dtype=int)
        for S, plist in byS_p.items():
            llist = list(byS_l[S])
            rng.shuffle(llist)
            for i, j in zip(plist, llist):
                p0 = self.pO[i][0]
                L0 = rng.choice(self.lO[j])
                for t in range(self.nK):
                    s[self.pperm[t][p0]] = self.lperm[t][L0]
        assert (s >= 0).all() and len(set(s.tolist())) == self.N
        return s

    def check_equivariant(self, s):
        for t in range(self.nK):
            assert all(s[self.pperm[t][p]] == self.lperm[t][s[p]] for p in range(self.N))
        return True

    def sources(self):
        src = [(O[0], len(O)) for O in self.pO] + [(self.N + O[0], len(O)) for O in self.lO]
        return src

    def write_srcs(self, path, src):
        with open(path, 'w') as fh:
            fh.write('%d\n' % len(src))
            for v, w in src:
                fh.write('%d %d\n' % (v, w))

    def write_base(self, path, s_list, labels, M1, M2, tvec):
        """hop h: dart p -> N+s_h[p] with voltage (tvec[h], labels[h][porb[p]]) in Z_M1 x Z_M2."""
        N = self.N
        with open(path, 'w') as fh:
            fh.write('%d %d %d %d\n' % (2 * N, M1, M2, len(self.flag_strs) + N * len(s_list)))
            fh.writelines(self.flag_strs)
            for h, s in enumerate(s_list):
                lab = labels[h]
                for p in range(N):
                    fh.write('%d %d %d %d\n' % (p, N + int(s[p]), tvec[h] % M1, int(lab[self.porb[p]]) % M2))


def run_liftw(base_path, src_path, D=8):
    out = subprocess.run([LIFTW, base_path, str(D), src_path], capture_output=True, text=True).stdout
    return int(out.split()[1]), out

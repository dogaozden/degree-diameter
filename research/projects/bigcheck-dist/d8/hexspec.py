"""Helpers for building cyclic-lift specs (bcd.c "lift" format) on the split Cayley hexagon H(q).

Base vertex numbering: points 0..N-1, lines N..2N-1 (hexgen indexing). A lift spec is a list of base edges (u, v, a):
lift edges (u, g) ~ (v, g + a mod M). The Singer torus tau (singer.py) acts freely on points and lines; a voltage
assignment that is tau-invariant (same voltage on e and tau(e)) makes "aut 1 <tau on base> <zeros>" an automorphism,
and bcd then needs only one source per tau-orbit.

    import hexspec as hs
    H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
    edges = [...]                       # (u, v, a) with u a point id, v = N + line id
    hs.write_spec('x.spec', H, M, edges, tau_invariant=True)
    cost = hs.bcd_cost('x.spec', d=8, D=8)   # pairs at distance > D summed over orbit representatives (0 = valid)

Files: H.lines[l] = the q+1 points of line l; H.plines[p] = the q+1 lines through p; H.coord[p] = 7 coordinates;
H.tp, H.tl = tau on points / lines; H.KA = order of tau; H.porb / H.lorb = orbit ids; H.prep / H.lrep = smallest
member of each orbit; H.ppos[p] = e with p = tau^e(prep[porb[p]]).
"""
import os
import subprocess

import numpy as np

BCD = os.environ.get("BCD", "/tmp/bcd")


class Hex:
    def __init__(self, hexbin, singerbin=None):
        raw = open(hexbin, "rb").read()
        q, N, L = np.frombuffer(raw[:12], dtype=np.int32)
        self.q, self.N = int(q), int(N)
        self.lines = np.frombuffer(raw[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
        self.coord = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
        pl = [[] for _ in range(self.N)]
        for l, pts in enumerate(self.lines):
            for p in pts:
                pl[p].append(l)
        self.plines = np.array(pl, dtype=np.int64)
        if singerbin:
            r = open(singerbin, "rb").read()
            n2, KA = np.frombuffer(r[:8], dtype=np.int32)
            assert n2 == self.N
            self.KA = int(KA)
            self.tp = np.frombuffer(r[8:8 + 4 * self.N], dtype=np.int32).astype(np.int64)
            self.tl = np.frombuffer(r[8 + 4 * self.N:8 + 8 * self.N], dtype=np.int32).astype(np.int64)
            self.porb, self.ppos, self.prep = self._orbits(self.tp)
            self.lorb, self.lpos, self.lrep = self._orbits(self.tl)

    def _orbits(self, t):
        N = self.N
        orb = -np.ones(N, dtype=np.int64); pos = np.zeros(N, dtype=np.int64); reps = []
        for x in range(N):
            if orb[x] >= 0:
                continue
            y = x
            for e in range(self.KA):
                orb[y] = len(reps); pos[y] = e; y = t[y]
            assert y == x
            reps.append(x)
        return orb, pos, np.array(reps, dtype=np.int64)

    def tau_power_points(self, e):
        p = np.arange(self.N)
        for _ in range(e % self.KA):
            p = self.tp[p]
        return p

    def base_tau(self):
        """tau on base vertices (points then lines)"""
        return np.concatenate([self.tp, self.N + self.tl])


def write_spec(path, H, M, edges, tau_invariant=True):
    """edges: iterable of (u, v, a). If tau_invariant, the torus automorphism line is added (bcd checks it)."""
    edges = list(edges)
    with open(path, "w") as f:
        f.write(f"bcd-lift 1\ngroup cyclic {M}\nvertices {2 * H.N}\nedges {len(edges)}\n")
        f.write("".join(f"{u} {v} {a % M}\n" for u, v, a in edges))
        if tau_invariant:
            f.write("aut 1\n" + " ".join(map(str, H.base_tau())) + "\n" + " ".join(["0"] * (2 * H.N)) + "\n")
        f.write("end\n")


def bcd_cost(spec, d, D, threads=1):
    out = subprocess.run([BCD, "lift", spec, str(d), str(D), "--cost", "--threads", str(threads)],
                         capture_output=True, text=True)
    for ln in out.stdout.splitlines():
        if ln.startswith("COST"):
            return int(ln.split()[1])
    raise RuntimeError(out.stdout + out.stderr)


def bcd_check(spec, d, D, threads=1):
    """full check; returns (valid, last lines of output)"""
    out = subprocess.run([BCD, "lift", spec, str(d), str(D), "--threads", str(threads)], capture_output=True, text=True)
    return ("RESULT VALID" in out.stdout), out.stdout.strip().splitlines()[-3:]


def equivariant_bijection(H, rng):
    """a random tau-equivariant bijection points -> lines: sigma(tau^e prep[o]) = tau^(e + t_o) lrep[pi(o)]"""
    NO = len(H.prep)
    pi = rng.permutation(NO); t = rng.integers(0, H.KA, NO)
    # tau powers on lines
    TL = [np.arange(H.N)]
    for _ in range(H.KA - 1):
        TL.append(H.tl[TL[-1]])
    sig = np.empty(H.N, dtype=np.int64)
    for p in range(H.N):
        o, e = H.porb[p], H.ppos[p]
        sig[p] = TL[(e + t[o]) % H.KA][H.lrep[pi[o]]]
    return sig

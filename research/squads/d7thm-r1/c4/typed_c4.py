#!/usr/bin/env python3
"""Card c4 of squad round d7thm-r1: end-to-end test of typed level layouts with the freed sets of BRIEF.md.

Usage: python3 typed_c4.py q [--k 2 3] [--seed 1] [--controls] [--hubs]
Reads hex/hex_q{q}.bin (from hexgen2.c), builds S, P_S, v, L_v, W, S_0, R_H, R_L, an elliptic section R with a
sigma as in the brief, the typed level graph for each k, writes edge lists and runs apsp_mt.
"""
import os, sys, json, random, subprocess, argparse
from collections import deque
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = []


def log(msg):
    print(msg, flush=True)
    LOG.append(msg)


class Field:
    def __init__(self, q):
        self.q = q
        if q in (3, 5, 7):
            self.ADD = np.array([[(a + b) % q for b in range(q)] for a in range(q)], dtype=np.int64)
            self.MUL = np.array([[(a * b) % q for b in range(q)] for a in range(q)], dtype=np.int64)
        elif q == 4:  # a0 + a1*2 with x^2 = x + 1
            def m4(a, b):
                a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
                return ((a0 * b0 + a1 * b1) % 2) + 2 * ((a0 * b1 + a1 * b0 + a1 * b1) % 2)
            self.ADD = np.array([[a ^ b for b in range(4)] for a in range(4)], dtype=np.int64)
            self.MUL = np.array([[m4(a, b) for b in range(4)] for a in range(4)], dtype=np.int64)
        else:
            raise SystemExit("unsupported q")
        A, M = self.ADD, self.MUL
        self.NEG = np.array([[b for b in range(q) if A[a, b] == 0][0] for a in range(q)], dtype=np.int64)
        self.INV = np.array([0] + [[b for b in range(q) if M[a, b] == 1][0] for a in range(1, q)], dtype=np.int64)
        for a in range(q):
            for b in range(q):
                for c in range(q):
                    assert M[a, A[b, c]] == A[M[a, b], M[a, c]] and M[M[a, b], c] == M[a, M[b, c]]
        for a in range(1, q):
            assert M[a, self.INV[a]] == 1

    def add(self, a, b): return self.ADD[a, b]
    def mul(self, a, b): return self.MUL[a, b]
    def sub(self, a, b): return self.ADD[a, self.NEG[b]]
    def neg(self, a): return self.NEG[a]
    def inv(self, a): return self.INV[a]


class Hex:
    def __init__(self, q):
        self.q = q
        self.F = Field(q)
        path = os.path.join(HERE, "hex", f"hex_q{q}.bin")
        hdr = np.fromfile(path, dtype=np.int32, count=3)
        assert int(hdr[0]) == q
        self.N, self.L = int(hdr[1]), int(hdr[2])
        self.lines = np.fromfile(path, dtype=np.int32, count=self.L * (q + 1), offset=12) \
            .reshape(self.L, q + 1).astype(np.int64)
        self.C = np.fromfile(path, dtype=np.uint8, count=self.N * 7, offset=12 + 4 * self.L * (q + 1)) \
            .reshape(self.N, 7).astype(np.int64)
        lop = [[] for _ in range(self.N)]
        for l in range(self.L):
            for p in self.lines[l]:
                lop[p].append(l)
        assert all(len(x) == q + 1 for x in lop)
        self.lop = [np.array(x, dtype=np.int64) for x in lop]

    def lin(self, a):
        F, C = self.F, self.C
        acc = np.zeros(self.N, dtype=np.int64)
        for i in range(7):
            if int(a[i]) % self.q:
                acc = F.add(acc, F.mul(int(a[i]), C[:, i]))
        return acc

    def quadric(self):
        F, C = self.F, self.C
        t = F.add(F.add(F.mul(C[:, 0], C[:, 4]), F.mul(C[:, 1], C[:, 5])), F.mul(C[:, 2], C[:, 6]))
        return F.sub(t, F.mul(C[:, 3], C[:, 3]))

    def plucker_ok(self):
        F = self.F
        eqs = [(1, 2, 3, 4), (5, 4, 3, 2), (2, 0, 3, 5), (6, 5, 3, 0), (0, 1, 3, 6), (4, 6, 3, 1)]
        for l in range(self.L):
            pts = self.lines[l]
            x, y = self.C[pts[0]], self.C[pts[1]]
            p = lambda i, j: F.sub(F.mul(x[i], y[j]), F.mul(x[j], y[i]))
            for (a, b, c, d) in eqs:
                if p(a, b) != p(c, d):
                    return False
        return True

    def bfs(self, src):
        N = self.N
        dist = np.full(N + self.L, -1, dtype=np.int64)
        dist[src] = 0
        dq = deque([src])
        while dq:
            x = dq.popleft()
            dx = dist[x]
            nb = (N + self.lop[x]) if x < N else self.lines[x - N]
            for y in nb:
                if dist[y] < 0:
                    dist[y] = dx + 1
                    dq.append(y)
        return dist


def build_sets(H, seed):
    q, N, L, lines, C = H.q, H.N, H.L, H.lines, H.C
    F = H.F
    chk = {}

    def check(name, ok):
        chk[name] = bool(ok)
        log(f"    [{'PASS' if ok else 'FAIL'}] {name}")

    check("H(q) points all singular (Q=0)", np.all(H.quadric() == 0))
    check(f"H(q): {N} lines, q+1 points per line, q+1 lines per point", L == N and
          all(len(set(lines[l])) == q + 1 for l in range(L)))
    check("H(q): Plucker equations of Tits hold on every line", H.plucker_ok())

    e1 = int(np.nonzero((C == [0, 1, 0, 0, 0, 0, 0]).all(axis=1))[0][0])
    e6 = int(np.nonzero((C == [0, 0, 0, 0, 0, 0, 1]).all(axis=1))[0][0])
    common = sorted(set(H.lop[e1].tolist()) & set(H.lop[e6].tolist()))
    check("v: the line through e1 and e6 exists and is unique", len(common) == 1)
    v = common[0]

    odd = (q % 2 == 1)
    if odd:
        squares = {int(F.mul(x, x)) for x in range(1, q)}
        c = min(x for x in range(1, q) if int(F.neg(x)) not in squares)  # -c non-square
        log(f"    c = {c}  (-c = {int(F.neg(c))} is a non-square)")

        def Gf(a, b, c0, c1):
            t = F.mul(F.add(F.mul(c0, a), F.mul(c1, b)), F.add(F.mul(a, a), F.mul(c, F.mul(b, b))))
            return F.sub(t, F.mul(b, F.mul(b, b)))

        def Fden(al, be):
            return F.add(F.mul(al, al), F.mul(c, F.mul(be, be)))

        def plane(al, be):
            return [1, 0, al, 0, c, be, 0]

        def nu_parts(x):
            x2, x3, x4, x5 = x[2], x[3], x[4], x[5]
            num = F.sub(F.mul(x2, x3), F.mul(x4, x5))
            den = F.add(F.mul(c, F.mul(x2, x2)), F.mul(x5, x5))
            return num, den
    else:
        delta = min(x for x in range(q) if int(F.add(x, F.mul(x, x))) == 1)  # absolute trace 1
        log(f"    delta = {delta}  (absolute trace 1)")

        def Gf(a, b, c0, c1):
            t = F.mul(F.add(F.mul(c0, a), F.mul(c1, b)),
                      F.add(F.add(F.mul(a, a), F.mul(a, b)), F.mul(delta, F.mul(b, b))))
            return F.add(t, F.mul(b, F.mul(b, b)))

        def Fden(al, be):
            return F.add(F.add(F.mul(al, al), F.mul(al, be)), F.mul(delta, F.mul(be, be)))

        def plane(al, be):
            return [1, 0, al, 1, delta, be, 0]

        def nu_parts(x):
            x2, x3, x4, x5 = x[2], x[3], x[4], x[5]
            num = F.add(F.add(F.mul(x2, x3), F.mul(x2, x4)), F.mul(x4, x5))
            den = F.add(F.add(F.mul(delta, F.mul(x2, x2)), F.mul(x2, x5)), F.mul(x5, x5))
            return num, den

    def nu(p):
        num, den = nu_parts(C[p])
        assert int(den) != 0, "nu undefined"
        return int(F.mul(num, F.inv(den)))

    # G(a,b) zero-free on F^2 minus 0
    gpair = None
    for c0 in range(q):
        for c1 in range(q):
            if all(int(Gf(a, b, c0, c1)) != 0 for a in range(q) for b in range(q) if (a, b) != (0, 0)):
                gpair = (c0, c1)
                break
        if gpair:
            break
    check("G zero-free on F^2 minus 0 for some (c0,c1)", gpair is not None)
    c0, c1 = gpair
    log(f"    (c0,c1) = {gpair}")

    def Fz(al, be):
        den = int(Fden(al, be))
        assert den != 0
        return int(F.mul(Gf(al, be, c0, c1), F.inv(den)))

    # S = lines of H in Pi, P_S, v
    inPi = H.lin(plane(0, 0)) == 0
    onS = inPi[lines].all(axis=1)
    S = [int(x) for x in np.nonzero(onS)[0]]
    check(f"|S| = q^3+1 = {q**3+1}", len(S) == q ** 3 + 1)
    PS = np.nonzero(inPi)[0]
    PS_lines = np.unique(lines[np.array(S)].ravel())
    check(f"P_S = points of H in Pi, |P_S| = (q+1)(q^3+1) = {(q+1)*(q**3+1)}",
          np.array_equal(PS, PS_lines) and len(PS) == (q + 1) * (q ** 3 + 1))
    cntS = np.zeros(N, dtype=np.int64)
    for l in S:
        cntS[lines[l]] += 1
    check("S is a spread of P_S (each point of P_S on exactly one S-line)", np.all(cntS[PS] == 1))
    check("v is in S", onS[v])

    vpts = set(lines[v].tolist())
    Lv = [l for l in range(L) if l != v and any(p in vpts for p in lines[l])]
    check(f"|L_v| = q(q+1) = {q*(q+1)}", len(Lv) == q * (q + 1))

    dist_v = H.bfs(N + v)
    dP = dist_v[:N]
    check("points at distance <=3 from v are exactly X2=X5=0",
          np.array_equal(dP <= 3, (C[:, 2] == 0) & (C[:, 5] == 0)))
    free = np.nonzero((~inPi) & (dP == 5))[0]
    check(f"free points (not in Pi, distance 5 from v) = q^3(q^2-1) = {q**3*(q*q-1)}",
          len(free) == q ** 3 * (q * q - 1))

    # W
    Wz = {}
    n_S_in_z = 0
    n_Sz_meet_v = 0
    for al in range(q):
        for be in range(q):
            if (al, be) == (0, 0):
                continue
            inz = H.lin(plane(al, be)) == 0
            Sz = np.nonzero(inz[lines].all(axis=1))[0]
            fz = Fz(al, be)
            lst = []
            for l in Sz:
                l = int(l)
                if l == v:
                    continue
                if any(p in vpts for p in lines[l]):
                    n_Sz_meet_v += 1
                pin = [int(p) for p in lines[l] if inPi[p]]
                if len(pin) != 1:
                    n_S_in_z += 1
                    continue
                if nu(pin[0]) == fz:
                    lst.append(l)
            Wz[(al, be)] = lst
    Wall = sorted(set(x for lst in Wz.values() for x in lst))
    total_Wz = sum(len(x) for x in Wz.values())
    log(f"    |W_z| per z: min {min(len(x) for x in Wz.values())} max {max(len(x) for x in Wz.values())}; "
        f"S_z lines inside Pi (excluded) {n_S_in_z}; S_z lines (not v) meeting v {n_Sz_meet_v}")
    check(f"|W| = q^2(q^2-1) = {q*q*(q*q-1)} (W_z disjoint)", len(Wall) == q * q * (q * q - 1) and total_Wz == len(Wall))
    cntW = np.zeros(N, dtype=np.int64)
    for l in Wall:
        cntW[lines[l]] += 1
    check("every free point is on exactly one W-line", np.all(cntW[free] == 1))

    Sm = [m for m in S if m != v]
    nuline = {}
    const_ok = True
    for m in Sm:
        vals = set(nu(p) for p in lines[m])
        if len(vals) != 1:
            const_ok = False
        nuline[m] = vals.pop() if len(vals) == 1 else None
    check("nu is constant on every line of S other than v", const_ok)
    meetW = {m: int(sum(cntW[p] for p in lines[m])) for m in Sm}
    check("every S-line other than v meets 0 or q+1 W-lines (one at each point)",
          all(meetW[m] == 0 or (meetW[m] == q + 1 and all(cntW[p] == 1 for p in lines[m])) for m in Sm))
    S0 = [m for m in Sm if meetW[m] == 0]
    check(f"exactly q^2 = {q*q} S-lines (not v) meet no W-line, and they are the nu=0 ones",
          len(S0) == q * q and set(S0) == {m for m in Sm if nuline[m] == 0})

    RL = sorted(set(Lv) | set(Wall) | set(S0))
    check(f"R_L = L_v + W + S_0 is a disjoint union of size q^4+q^2+q = {q**4+q*q+q}",
          len(RL) == q ** 4 + q * q + q and len(Lv) + len(Wall) + len(S0) == len(RL))

    def is_dual_seg(G):
        cnt = np.zeros(N, dtype=np.int64)
        for l in G:
            cnt[lines[l]] += 1
        Ga = np.array(G, dtype=np.int64)
        return bool(np.all((cnt[lines[Ga]] >= 2).sum(axis=1) <= 1))

    def is_seg(P):
        inP = np.zeros(N, dtype=bool)
        inP[np.array(P, dtype=np.int64)] = True
        active = inP[lines].sum(axis=1) >= 2
        return all(int(active[H.lop[p]].sum()) <= 1 for p in P)

    check("R_L is a dual segment set", is_dual_seg(RL))
    cntRL = np.zeros(N, dtype=np.int64)
    for l in RL:
        cntRL[lines[l]] += 1
    check("every point of H(q) is on a line of R_L", np.all(cntRL >= 1))
    RLa = np.array(RL, dtype=np.int64)
    inRL = np.zeros(L, dtype=bool)
    inRL[RLa] = True
    addable = 0
    for m in range(L):
        if inRL[m]:
            continue
        cnt2 = cntRL.copy()
        cnt2[lines[m]] += 1
        Gm = np.append(RLa, m)
        if np.all((cnt2[lines[Gm]] >= 2).sum(axis=1) <= 1):
            addable += 1
    check("R_L is maximal: no line outside R_L can be added", addable == 0)
    check(f"R_H = P_S is a segment set of size (q+1)(q^3+1)", is_seg([int(p) for p in PS]))

    # elliptic quadric section R (points of H in a 3-space Sigma, q^2+1 points, no line inside)
    rng = random.Random(seed)
    mask = None
    for _ in range(200000):
        forms = [[rng.randrange(q) for _ in range(7)] for _ in range(3)]
        if any(all(x == 0 for x in f) for f in forms):
            continue
        vals = [H.lin(f) for f in forms]
        m_ = (vals[0] == 0) & (vals[1] == 0) & (vals[2] == 0)
        if int(m_.sum()) != q * q + 1:
            continue
        if m_[lines].all(axis=1).any():
            continue
        mask = m_
        break
    check("found a 3-space Sigma with |Sigma cap H| = q^2+1 and no line inside", mask is not None)
    R = [int(x) for x in np.nonzero(mask)[0]]
    opp_ok = True
    for x in R:
        d = H.bfs(x)
        for y in R:
            if y != x and d[y] != 6:
                opp_ok = False
    check("R: pairwise opposite (distance 6 in the incidence graph)", opp_ok)

    Rstar = rng.sample(S, q * q + 1)
    perm = list(Rstar)
    rng.shuffle(perm)
    sig = -np.ones(N, dtype=np.int64)
    usedC = np.zeros(N, dtype=bool)
    usedM = np.zeros(L, dtype=bool)
    usedC[R] = True
    usedM[Rstar] = True
    sig_ok = True
    for x, fx in zip(R, perm):
        Cx = sorted({int(p) for l in H.lop[x] for p in lines[l] if p != x})
        Mx = sorted({int(l2) for p in lines[fx] for l2 in H.lop[p] if l2 != fx})
        if len(Cx) != q * (q + 1) or len(Mx) != q * (q + 1) or usedC[Cx].any() or usedM[Mx].any():
            sig_ok = False
            break
        rng.shuffle(Mx)
        for p, l2 in zip(Cx, Mx):
            sig[p] = l2
        usedC[Cx] = True
        usedM[Mx] = True
        sig[x] = fx
    restP = [p for p in range(N) if not usedC[p]]
    restL = [l for l in range(L) if not usedM[l]]
    sig_ok = sig_ok and len(restP) == len(restL) == q * q * (q ** 3 - 1)
    rng.shuffle(restL)
    for p, l in zip(restP, restL):
        sig[p] = l
    check("sigma: R -> R* via f, C(x) -> lines meeting f(x), rest -> rest (bijection of points onto lines)",
          sig_ok and sorted(sig.tolist()) == list(range(N)) and set(sig[R].tolist()) == set(Rstar))
    inv = np.empty(L, dtype=np.int64)
    inv[sig] = np.arange(N)

    sizes = dict(S=len(S), PS=len(PS), Lv=len(Lv), W=len(Wall), S0=len(S0), RL=len(RL), RH=len(PS),
                 R=len(R), Rstar=len(Rstar), free=len(free))
    log(f"    sizes: {sizes}")
    return dict(q=q, c=(c if odd else None), delta=(delta if not odd else None), gpair=gpair, v=v, S=S,
                PS=[int(p) for p in PS], Lv=Lv, W=Wall, S0=S0, RL=RL, R=R, Rstar=[int(x) for x in Rstar],
                sig=sig, inv=inv, checks=chk, sizes=sizes, is_dual_seg=is_dual_seg, is_seg=is_seg,
                inRL=inRL)


def predicted_slots(q, k):
    """Per-level predictions from the friendly / non-friendly rule (types H for even j, D for odd j)."""
    RH, RLs, ns = (q + 1) * (q ** 3 + 1), q ** 4 + q * q + q, q * q + 1
    L = 2 * k + 1
    isH = lambda j: j % 2 == 0

    def contrib(tA, tB):  # freed count for a transition from type tA to type tB
        if tA == tB:
            return ns
        return RH if tA == 'H' else RLs

    typ = lambda j: 'H' if isH(j) else 'D'
    alpha = [sum(contrib(typ(j), typ((j + i) % L)) for i in range(1, k + 1)) for j in range(L)]
    beta = [sum(contrib(typ((j - i) % L), typ(j)) for i in range(1, k + 1)) for j in range(L)]
    return alpha, beta


def build_edges(H, S_, k, extra_HD=(), extra_DH=(), hubs=False, hubseed=1):
    q, N, L, lines = H.q, H.N, H.L, H.lines
    NLv = 2 * k + 1
    per = 2 * N
    vp = lambda p, j: j * per + p
    vl = lambda l, j: j * per + N + l
    isH = lambda j: j % 2 == 0
    freedHD = np.zeros(N, dtype=bool)
    freedHD[np.array(S_['PS'], dtype=np.int64)] = True
    freedHD[np.array(list(extra_HD), dtype=np.int64)] = True
    freedDH = np.zeros(L, dtype=bool)
    freedDH[np.array(S_['RL'], dtype=np.int64)] = True
    freedDH[np.array(list(extra_DH), dtype=np.int64)] = True
    freedR = np.zeros(N, dtype=bool)
    freedR[np.array(S_['R'], dtype=np.int64)] = True
    freedRs = np.zeros(L, dtype=bool)
    freedRs[np.array(S_['Rstar'], dtype=np.int64)] = True
    sig, inv = S_['sig'], S_['inv']
    E = []
    dout = np.zeros(NLv, dtype=np.int64)
    din = np.zeros(NLv, dtype=np.int64)
    slotA = [set() for _ in range(NLv)]
    slotB = [set() for _ in range(NLv)]
    ls = np.repeat(np.arange(L), q + 1)
    ps = lines.ravel()
    for j in range(NLv):
        E.append(np.stack([vp(ps, j), vl(ls, j)], axis=1))  # incidences inside level j
    ar_N, ar_L = np.arange(N), np.arange(L)
    for j in range(NLv):
        for i in range(1, k + 1):
            j2 = (j + i) % NLv
            if isH(j) and isH(j2):
                src, dst, fr = vp(ar_N, j), vl(sig, j2), freedR
            elif (not isH(j)) and (not isH(j2)):
                src, dst, fr = vl(ar_L, j), vp(inv, j2), freedRs
            elif isH(j):  # friendly H -> D, identity on points
                src, dst, fr = vp(ar_N, j), vp(ar_N, j2), freedHD
            else:  # friendly D -> H, identity on lines
                src, dst, fr = vl(ar_L, j), vl(ar_L, j2), freedDH
            keep = ~fr
            E.append(np.stack([src[keep], dst[keep]], axis=1))
            nd = int((~keep).sum())
            dout[j] += nd
            din[j2] += nd
            for a in np.nonzero(~keep)[0]:
                slotA[j].add(int(src[a]))
                slotB[j2].add(int(dst[a]))
    n = NLv * per
    edges = np.concatenate(E)
    extra = []
    if hubs:
        rng = random.Random(hubseed)
        Bh = [n + h for h in range(7)]
        Ah = [n + 7 + g for g in range(7)]
        for j in range(NLv):
            assert len(slotA[j]) >= 7 and len(slotB[j]) >= 7
            pa = rng.sample(sorted(slotA[j]), 7)
            for h in range(7):
                extra.append((Bh[h], pa[h]))
            pb = rng.sample(sorted(slotB[j]), 7)
            for g in range(7):
                extra.append((Ah[g], pb[g]))
        for nv in range(1, 8):  # Fano plane PG(2,2): point x on line nv iff popcount(nv & x) even
            for x in range(1, 8):
                if bin(nv & x).count("1") % 2 == 0:
                    extra.append((Bh[x - 1], Ah[nv - 1]))
        n += 14
        edges = np.concatenate([edges, np.array(extra, dtype=np.int64)])
    return n, edges, dout, din


def write_and_run(n, edges, path, d, D=7):
    with open(path, "w") as f:
        f.write(f"{n}\n")
        np.savetxt(f, edges, fmt="%d")
    cmd = ["timeout", "900", "nice", "-n", "10", os.path.join(HERE, "apsp_mt"), path, str(d), str(D), "1"]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    return out


def parse_apsp(out):
    diam = None
    for line in out.splitlines():
        if "diameter=" in line:
            diam = int(line.split("diameter=")[1].split()[0])
    valid = "RESULT VALID" in out
    return valid, diam, out.strip().splitlines()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("q", type=int)
    ap.add_argument("--k", type=int, nargs="+", default=[2, 3])
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--hubs", action="store_true")
    args = ap.parse_args()
    q = args.q
    tmp = os.path.join(HERE, "tmp")
    os.makedirs(tmp, exist_ok=True)
    results = {"q": q, "seed": args.seed, "configs": {}}

    log(f"=== q={q} ===")
    H = Hex(q)
    log(f"  loaded H({q}): N={H.N} points, L={H.L} lines")
    S_ = build_sets(H, args.seed)
    results["set_checks"] = S_["checks"]
    results["sizes"] = S_["sizes"]
    RLl = len(S_["RL"]); RHl = len(S_["PS"])
    assert RHl == (q + 1) * (q ** 3 + 1) and RLl == q ** 4 + q * q + q

    for k in args.k:
        log(f"  --- k={k}, L={2*k+1} levels ---")
        cfg = {}
        pa, pb = predicted_slots(q, k)
        n, edges, dout, din = build_edges(H, S_, k)
        path = os.path.join(tmp, f"edges_q{q}_k{k}_s{args.seed}.txt")
        out = write_and_run(n, edges, path, q + 1 + k)
        valid, diam, lines_out = parse_apsp(out)
        log("    apsp: " + " | ".join(lines_out[-2:]))
        cfg["n"] = n
        cfg["apsp"] = lines_out
        cfg["valid"] = valid
        cfg["diameter"] = diam
        alpha = [int(x) for x in dout]
        beta = [int(x) for x in din]
        cfg["alpha"] = alpha
        cfg["beta"] = beta
        cfg["pred_alpha"] = pa
        cfg["pred_beta"] = pb
        cfg["min_alpha"] = min(alpha)
        cfg["min_beta"] = min(beta)
        ns = q * q + 1
        if k == 2:
            pred_min = RLl + ns
        else:
            pred_min = RHl + 2 * ns
            pred_min_b = RLl + 2 * ns
        cfg["pred_min_alpha"] = pred_min if k == 2 else RHl + 2 * ns
        cfg["pred_min_beta"] = RLl + ns if k == 2 else RLl + 2 * ns
        cfg["slots_match_pred"] = (alpha == pa and beta == pb)
        log(f"    alpha={alpha} beta={beta}")
        log(f"    min alpha={min(alpha)} (pred {cfg['pred_min_alpha']}), min beta={min(beta)} (pred {cfg['pred_min_beta']}); "
            f"per-level prediction match: {cfg['slots_match_pred']}")
        if args.controls:
            # control A: one extra line in R_L breaking the dual segment property
            cand = [m for m in range(H.L) if not S_["inRL"][m]]
            m_extra = None
            for m in cand:
                if not S_["is_dual_seg"](S_["RL"] + [m]):
                    m_extra = m
                    break
            assert m_extra is not None
            n2, e2, _, _ = build_edges(H, S_, k, extra_DH=[m_extra])
            out2 = write_and_run(n2, e2, os.path.join(tmp, f"edges_q{q}_k{k}_s{args.seed}_ctrlline.txt"), q + 1 + k)
            v2, d2, lo2 = parse_apsp(out2)
            cfg["ctrl_line"] = {"line": int(m_extra), "valid": v2, "diameter": d2, "apsp": lo2}
            log(f"    control (extra line in R_L, breaks dual segment): VALID={v2} diameter={d2}")
            # control B: one extra point in R_H breaking the segment property
            pts_out = [p for p in range(H.N) if p not in set(S_["PS"])]
            p_extra = None
            for p in pts_out:
                if not S_["is_seg"](S_["PS"] + [p]):
                    p_extra = p
                    break
            assert p_extra is not None
            n3, e3, _, _ = build_edges(H, S_, k, extra_HD=[p_extra])
            out3 = write_and_run(n3, e3, os.path.join(tmp, f"edges_q{q}_k{k}_s{args.seed}_ctrlpoint.txt"), q + 1 + k)
            v3, d3, lo3 = parse_apsp(out3)
            cfg["ctrl_point"] = {"point": int(p_extra), "valid": v3, "diameter": d3, "apsp": lo3}
            log(f"    control (extra point in R_H, breaks segment): VALID={v3} diameter={d3}")
        if args.hubs and q == 5 and k == 2:
            n4, e4, _, _ = build_edges(H, S_, k, hubs=True, hubseed=args.seed)
            out4 = write_and_run(n4, e4, os.path.join(tmp, f"edges_q{q}_k{k}_s{args.seed}_hubs.txt"), q + 1 + k)
            v4, d4, lo4 = parse_apsp(out4)
            cfg["hubs"] = {"n": n4, "valid": v4, "diameter": d4, "apsp": lo4}
            log(f"    hubs: n={n4} VALID={v4} diameter={d4}")
            log("    " + " | ".join(lo4[-2:]))
        results["configs"][f"k{k}"] = cfg
        log(f"  k={k}: apsp VALID={valid} diameter={diam} n={n}")

    out_path = os.path.join(HERE, f"result_q{q}_s{args.seed}.json")
    with open(out_path, "w") as f:
        json.dump(results, f, indent=1, default=str)
    log(f"  wrote {out_path}")


if __name__ == "__main__":
    main()

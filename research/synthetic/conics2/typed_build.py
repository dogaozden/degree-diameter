#!/usr/bin/env python3
"""typed_build.py (research/synthetic/conics2/README.md): the typed level layouts of D7_HEXAGON.md Section 6 for any
number of levels L = 2r+1 and any type string (H = a copy of H(q), D = a copy of its dual), with the freed sets of
research/synthetic/CONICS.md Section 3.4 on the friendly transitions:
  R_H = the point set of the Hermitian spread S (the lines of H(q) in an elliptic hyperplane Pi), a segment set;
  R_L = the lines != v meeting a line v of S, plus the exact whisker set W of POLISHED.md Theorem 6.5 (q odd) or
        Theorem 6.14 (q even) relative to S and v: q(q^3+1) lines, a dual segment set (CONICS.md Lemma 3.1).
Theorem B of D7_HEXAGON.md repairs a friendly transition (identity matching) for any segment set (points, source of
type H) or dual segment set (lines, source of type D). The non-friendly transitions (H -> H: sigma, D -> D:
sigma^-1) free a set R' with sigma a local duality at R' (Theorem C), taken either from a lab "multi" solution (sigma
and R' listed, as research/frontier/sols/d16D7_hex13_R792_n4025508.sol) or built here from a pairwise opposite point
set R' and m lines of S (Corollary 5.3(a), sigma as in Proposition 5.2; used for q = 16). Everything is re-checked here:
R_H a segment set, R_L a dual segment set, W exact, R' non-collinear, sigma(R') non-concurrent, sigma a local duality at
every point of R', hub-graph degrees and same-side hub distances <= 6 in the hub graph alone.

Hubs (Definition 3.1): line-side hub h takes the h-th free A-slot of every level and point-side hub h the h-th free
B-slot (slot lists in a fixed order: transitions k = 1..r, elements by index). Hub graph: a random bipartite graph of
maximum degree q - r (configuration model, sides may differ, 2-switch repair of far pairs), or an explicit edge list.
Vertex numbering (as research/cell147/typedmirror/tm_build.py): (x, level j) = 2Nj + kind*N + x (kind 0 = point of H,
1 = line); line-side hubs 2NL + h, point-side hubs 2NL + KB + h.

usage: typed_build.py make HEXBIN TYPES NONFR HUBS OUT.sol OUT.edges [KB KA]
         NONFR: path of a multi .sol, or ovoid:FILE (whitespace-separated point indices, pairwise opposite)
         HUBS:  rand:SEED or file:PATH (first line K, then "a b" per edge)
       typed_build.py build HEXBIN SOL OUT.edges        (inputs named in SOL, by sha256, in the same directory)"""
import sys, os, hashlib
import numpy as np


# ---------------------------------------------------------------- fields (encoding of research/d10D7/hexgen2.c)
def field(q):
    p = next(d for d in range(2, q + 1) if q % d == 0)
    e = 1
    while p ** e < q:
        e += 1
    assert p ** e == q
    if e == 1:
        a = np.arange(q)
        return p, (a[:, None] + a[None, :]) % q, (a[:, None] * a[None, :]) % q
    poly = {4: [1, 1], 8: [1, 1, 0], 9: [1, 0], 16: [1, 1, 0, 0], 25: [2, 0], 27: [1, 2, 0], 32: [1, 0, 1, 0, 0]}[q]
    dig = lambda x: [(x // p ** i) % p for i in range(e)]
    und = lambda d: sum(v * p ** i for i, v in enumerate(d))
    ADD = np.zeros((q, q), np.int64); MUL = np.zeros((q, q), np.int64)
    for x in range(q):
        for y in range(q):
            a, b = dig(x), dig(y)
            ADD[x, y] = und([(s + t) % p for s, t in zip(a, b)])
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if f:
                    r[k] = 0
                    for i in range(e):
                        r[k - e + i] = (r[k - e + i] - f * poly[i]) % p
            MUL[x, y] = und(r[:e])
    return p, ADD, MUL


class F:
    def __init__(self, q):
        self.q = q
        self.p, self.A, self.M = field(q)
        self.NEG = np.array([int(np.nonzero(self.A[x] == 0)[0][0]) for x in range(q)])
        self.INV = np.array([0] + [int(np.nonzero(self.M[x] == 1)[0][0]) for x in range(1, q)])

    def add(self, *xs):
        o = xs[0]
        for x in xs[1:]:
            o = self.A[o, x]
        return o

    def mul(self, *xs):
        o = xs[0]
        for x in xs[1:]:
            o = self.M[o, x]
        return o

    def sub(self, a, b):
        return self.A[a, self.NEG[b]]

    def div(self, a, b):
        return self.M[a, self.INV[b]]


def tr(Fq, x):                                         # absolute trace x + x^2 + ... + x^(q/2), characteristic 2
    t, y, k = 0, int(x), 1
    while k < Fq.q:
        t = int(Fq.A[t, y]); y = int(Fq.M[y, y]); k *= 2
    return t


def params(Fq):
    """(c, c0, c1) of POLISHED.md Lemma 6.4 (q odd; the table values at q = 11, 13) or (delta, c0, c1) of Lemma 6.11
    (q even): G zero-free on F^2 minus 0."""
    q = Fq.q
    fixed = {11: (1, 1, 3), 13: (2, 1, 1)}
    els = range(q)
    if Fq.p == 2:
        cands = [d for d in range(1, q) if tr(Fq, d) == 1]
    else:
        sq = {int(Fq.M[x, x]) for x in range(1, q)}
        cands = [c for c in range(1, q) if int(Fq.NEG[c]) not in sq]
    a = np.repeat(np.arange(q), q); b = np.tile(np.arange(q), q); nz = (a != 0) | (b != 0); a, b = a[nz], b[nz]
    for c in ([fixed[q][0]] if q in fixed else cands):
        nrm = Fq.add(Fq.mul(a, a), Fq.mul(c, b, b)) if Fq.p != 2 else Fq.add(Fq.mul(a, a), Fq.mul(a, b), Fq.mul(c, b, b))
        for c0 in ([fixed[q][1]] if q in fixed else els):
            for c1 in ([fixed[q][2]] if q in fixed else els):
                lin = Fq.add(Fq.mul(c0, a), Fq.mul(c1, b))
                G = Fq.sub(Fq.mul(lin, nrm), Fq.mul(b, b, b)) if Fq.p != 2 else Fq.add(Fq.mul(lin, nrm), Fq.mul(b, b, b))
                if (G != 0).all():
                    return c, c0, c1
    raise SystemExit('no parameters')


# ---------------------------------------------------------------- the friendly freed sets
def friendly_sets(Fq, N, LP, PL, X):
    q = Fq.q
    c, c0, c1 = params(Fq)
    x = [X[:, i] for i in range(7)]
    if Fq.p != 2:
        lam = Fq.add(x[0], Fq.mul(c, x[4]))                          # Pi: x0 + c x4 = 0
    else:
        lam = Fq.add(x[3], x[0], Fq.mul(c, x[4]))                    # Pi: x3 = x0 + delta x4
    inPi = lam == 0
    S = np.nonzero(inPi[LP].all(1))[0]
    assert len(S) == q ** 3 + 1, len(S)
    e1 = np.nonzero((X == np.array([0, 1, 0, 0, 0, 0, 0])).all(1))[0][0]
    e6 = np.nonzero((X == np.array([0, 0, 0, 0, 0, 0, 1])).all(1))[0][0]
    (v,) = set(PL[e1].tolist()) & set(PL[e6].tolist())
    assert v in set(S.tolist())
    if Fq.p != 2:
        num = Fq.sub(Fq.mul(x[2], x[3]), Fq.mul(x[4], x[5]))
        den = Fq.add(Fq.mul(c, x[2], x[2]), Fq.mul(x[5], x[5]))
    else:
        num = Fq.add(Fq.mul(x[2], x[3]), Fq.mul(x[2], x[4]), Fq.mul(x[4], x[5]))
        den = Fq.add(Fq.mul(c, x[2], x[2]), Fq.mul(x[2], x[5]), Fq.mul(x[5], x[5]))
    W = []
    for al in range(q):
        for be in range(q):
            if (al, be) == (0, 0):
                continue
            inPz = Fq.add(lam, Fq.mul(al, x[2]), Fq.mul(be, x[5])) == 0
            Sz = np.nonzero(inPz[LP].all(1))[0]
            assert len(Sz) == q ** 3 + 1
            Sz = Sz[Sz != v]
            pts = LP[Sz]; msk = inPi[pts]
            assert (msk.sum(1) == 1).all()
            pz = pts[msk]                                            # the point of each line in Pi
            if Fq.p != 2:
                nrm = Fq.add(Fq.mul(al, al), Fq.mul(c, be, be))
                G = Fq.sub(Fq.mul(Fq.add(Fq.mul(c0, al), Fq.mul(c1, be)), nrm), Fq.mul(be, be, be))
            else:
                nrm = Fq.add(Fq.mul(al, al), Fq.mul(al, be), Fq.mul(c, be, be))
                G = Fq.add(Fq.mul(Fq.add(Fq.mul(c0, al), Fq.mul(c1, be)), nrm), Fq.mul(be, be, be))
            Fz = Fq.div(G, nrm)
            W.append(Sz[Fq.div(num[pz], den[pz]) == Fz])
    W = np.unique(np.concatenate(W))
    near = (x[2] == 0) & (x[5] == 0)                                 # distance <= 3 from v (Lemma 6.1(d))
    free = ~inPi & ~near
    cnt = np.zeros(N, np.int64); np.add.at(cnt, LP[W].reshape(-1), 1)
    assert len(W) == q * q * (q * q - 1) and (cnt[free] == 1).all(), 'exact whisker set check failed'
    Lv = sorted(set(PL[LP[v]].reshape(-1).tolist()) - {int(v)})
    RL = np.zeros(N, bool); RL[Lv] = True; RL[W] = True
    assert RL.sum() == q * (q ** 3 + 1)
    RH = np.zeros(N, bool); RH[LP[S].reshape(-1)] = True
    assert RH.sum() == (q + 1) * (q ** 3 + 1)
    cntL = RH[LP].sum(1)
    assert ((cntL[PL] >= 2).sum(1)[RH] <= 1).all(), 'R_H is not a segment set'
    cntP = RL[PL].sum(1)
    assert ((cntP[LP] >= 2).sum(1)[RL] <= 1).all(), 'R_L is not a dual segment set'
    print(f'q = {q}, {"(c, c0, c1)" if Fq.p != 2 else "(delta, c0, c1)"} = {(c, c0, c1)}; spread |S| = {len(S)}, v = {v}; '
          f'R_H = spread points ({RH.sum()}, segment set), R_L = lines meeting v + exact whiskers ({RL.sum()}, dual '
          f'segment set; |W| = {len(W)}, every free point on exactly one whisker)', flush=True)
    return RH, RL, S, int(v)


# ---------------------------------------------------------------- the non-friendly surgery
def sigma_from_ovoid(N, LP, PL, R, Rs):
    """Proposition 5.2 with no pairs at distance 4 (Corollary 5.3(a)): sigma(R[i]) = Rs[i], the points collinear with
    R[i] (by index) onto the lines concurrent with Rs[i] (by index), the remaining points onto the remaining lines (by
    index)."""
    sig = np.full(N, -1, np.int64); usedL = np.zeros(N, bool)
    for x, l in zip(R, Rs):
        G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x]); G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])
        assert (sig[G2x] < 0).all() and not usedL[G2l].any() and sig[x] < 0 and not usedL[l]
        sig[x] = l; usedL[l] = True; sig[G2x] = G2l; usedL[G2l] = True
    rest = np.nonzero(sig < 0)[0]; restL = np.nonzero(~usedL)[0]
    assert len(rest) == len(restL)
    sig[rest] = restL
    return sig


def main():
    mode = sys.argv[1]
    if mode == 'make':
        hexfn, T, nonfr, hubs, solout, outfn = sys.argv[2:8]
        want = (int(sys.argv[8]), int(sys.argv[9])) if len(sys.argv) > 9 else None
        hubE = None; hubK = None
        if hubs.startswith('file:'):
            hl = open(hubs[5:]).read().split('\n')
            hubK = (int(hl[0]), int(hl[0]))
            hubE = np.array([[int(t) for t in s.split()] for s in hl[1:] if s.strip()], dtype=np.int64)
        else:
            seed = int(hubs.split(':')[1])
    else:
        hexfn, mysol, outfn = sys.argv[2:5]; d = os.path.dirname(os.path.abspath(mysol))
        man = open(mysol).read().split('\n')
        assert man[0].split()[0] == 'typedherm2'
        T = man[0].split()[3]; li = 1
        w = man[li].split(); li += 1
        if w[1] == 'multi':
            nonfr = os.path.join(d, w[2])
            assert hashlib.sha256(open(nonfr, 'rb').read()).hexdigest() == w[3], ('sha256 mismatch', nonfr)
        else:
            nonfr = 'inline'; Rlist = [int(t) for t in man[li].split()[1:]]; li += 1
        assert man[li].split()[0] == 'hubs'; hubK = (int(man[li].split()[1]), int(man[li].split()[2])); li += 1
        nh = int(man[li].split()[1]); li += 1
        hubE = np.array([[int(t) for t in s.split()] for s in man[li:li + nh]], dtype=np.int64)
        want = None
    b = open(hexfn, 'rb').read()
    q, N, Lc = (int(t) for t in np.frombuffer(b[:12], dtype=np.int32))
    Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    print(f'{os.path.basename(hexfn)}: q = {q}, N = {N}, sha256 {hashlib.sha256(b).hexdigest()}', flush=True)
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p))
    PL = flat_l[order].reshape(N, Q1)
    Fq = F(q)
    L = len(T); assert L % 2 == 1 and set(T) <= {'H', 'D'}
    RM = (L - 1) // 2; Delta = q + 1 + RM; dh = Delta - L
    ty = [1 if t == 'D' else 0 for t in T]
    RH, RL, S, v = friendly_sets(Fq, N, LP, PL, X)
    # non-friendly: sigma (points -> lines) and R'
    if nonfr.startswith('ovoid:') or nonfr == 'inline':
        if nonfr != 'inline':
            Rlist = [int(t) for t in open(nonfr[6:]).read().split()]
        Rp = np.array(Rlist, dtype=np.int64)
        assert len(np.unique(Rp)) == len(Rp)
        # pairwise opposite: no point of R' within distance 4 of another (balls of radius 4 in the incidence graph)
        inRp = np.zeros(N, bool); inRp[Rp] = True
        for x in Rp:
            b2 = np.unique(LP[PL[x]].reshape(-1)); b4 = np.unique(LP[PL[b2].reshape(-1)].reshape(-1))
            assert inRp[b4].sum() == 1, ("R' not pairwise opposite at", x)
        Rs = np.array([l for l in S.tolist() if l != v][:len(Rp)], dtype=np.int64)  # m lines of the spread S
        sig = sigma_from_ovoid(N, LP, PL, Rp, Rs)
        nfdesc = f'ovoid {len(Rp)}'
    else:
        mt = open(nonfr).read().split('\n')
        assert mt[0].split()[0] == 'multi' and mt[1].split()[0] == 'freed' and int(mt[0].split()[1]) == q
        Rp = np.array([int(t) for t in mt[1].split()[1:]], dtype=np.int64)
        sig = np.array([int(t) for s in mt[3:] for t in s.split()], dtype=np.int64)
        nfdesc = 'multi'
    assert len(sig) == N and len(np.unique(sig)) == N
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    inRp = np.zeros(N, bool); inRp[Rp] = True
    inSR = np.zeros(N, bool); inSR[sig[Rp]] = True
    assert (inRp[LP].sum(1) <= 1).all(), "R' collinear"
    assert (inSR[PL].sum(1) <= 1).all(), "sigma(R') concurrent"
    for x in Rp:
        G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x]); l = sig[x]
        G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])
        assert np.array_equal(np.sort(sig[G2x]), G2l), ('local duality fails at', x)
    print(f"non-friendly ({nfdesc}): |R'| = {len(Rp)} non-collinear, sigma(R') non-concurrent, sigma a local duality "
          f"at all {len(Rp)}", flush=True)
    VID = lambda j, kind, x: j * 2 * N + kind * N + x
    out = []
    for j in range(L):
        out.append(np.stack([VID(j, 0, flat_p), VID(j, 1, flat_l)], axis=1).astype(np.int32))
    Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
    x = np.arange(N)
    for j in range(L):
        for k in range(1, RM + 1):
            j2 = (j + k) % L
            a, bk = ty[j], 1 - ty[j2]
            if a == bk:                                    # friendly: identity
                img = x; free = RH if a == 0 else RL
            elif a == 0:                                   # H -> H: sigma
                img = sig; free = inRp
            else:                                          # D -> D: sigma^-1
                img = sinv; free = inSR
            keep = ~free
            out.append(np.stack([VID(j, a, x[keep]), VID(j2, bk, img[keep])], axis=1).astype(np.int32))
            Aslots[j].append(VID(j, a, x[free])); Bslots[j2].append(VID(j2, bk, img[free]))
    Aslots = [np.concatenate(s) for s in Aslots]; Bslots = [np.concatenate(s) for s in Bslots]
    KB = min(len(s) for s in Aslots); KA = min(len(s) for s in Bslots)
    print(f'types {T}: free A-slots per level {[len(s) for s in Aslots]}, B-slots {[len(s) for s in Bslots]} -> at most '
          f'{KB} line-side and {KA} point-side hubs; hub-graph degree <= {dh}', flush=True)
    if hubK is not None:
        assert hubK[0] <= KB and hubK[1] <= KA; KB, KA = hubK
    elif want is not None:
        assert want[0] <= KB and want[1] <= KA; KB, KA = want
    print('hubs per side', KB, KA, flush=True)
    NV0 = 2 * N * L; n = NV0 + KB + KA
    for j in range(L):
        out.append(np.stack([NV0 + np.arange(KB), Aslots[j][:KB]], axis=1).astype(np.int32))        # line-side hubs
    for j in range(L):
        out.append(np.stack([NV0 + KB + np.arange(KA), Bslots[j][:KA]], axis=1).astype(np.int32))   # point-side hubs

    def nblist(a, b, Ka):                                  # neighbours b of each node a < Ka, padded (repeats) to dh
        o = np.argsort(a, kind='stable'); bs = b[o]
        stt = np.searchsorted(a[o], np.arange(Ka + 1)); dg = np.diff(stt)
        assert dg.min() >= 1
        return np.stack([bs[stt[:-1] + np.minimum(t, dg - 1)] for t in range(dh)], axis=1)

    def far_pairs(he, listing=False):                      # same-side hub pairs at distance > 6 in the hub graph
        bad = 0; lst = []
        for side in (0, 1):
            u, w_, K, Kv = (he[:, 0], he[:, 1], KB, KA) if side == 0 else (he[:, 1], he[:, 0], KA, KB)
            Mu, Mv = nblist(u, w_, K), nblist(w_, u, Kv)
            Wd = (K + 63) // 64; idx = np.arange(K)
            Bt = np.zeros((K, Wd), np.uint64)
            Bt[idx, idx // 64] |= np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
            for _ in range(3):
                U = Bt[Mv[:, 0]].copy()
                for t in range(1, dh):
                    U |= Bt[Mv[:, t]]
                Bn = Bt.copy()
                for t in range(dh):
                    Bn |= U[Mu[:, t]]
                Bt = Bn
            full = np.full(Wd, ~np.uint64(0), np.uint64)
            if K % 64:
                full[-1] = np.uint64((1 << (K % 64)) - 1)
            miss = Bt ^ full
            nz = miss[miss != 0]
            bad += int(sum(bin(int(t)).count('1') for t in nz))
            if listing:
                for r_, c_ in zip(*np.nonzero(miss)):
                    wv = int(miss[r_, c_])
                    lst += [(side, int(r_), 64 * int(c_) + i) for i in range(64) if wv >> i & 1]
        return (bad, lst) if listing else bad

    if hubE is None:
        # configuration model: the smaller side has degree dh, the larger side degrees as equal as possible (<= dh)
        rng = np.random.default_rng([seed, 7])
        big, small = (0, 1) if KB >= KA else (1, 0)
        Kb, Ks = (KB, KA) if big == 0 else (KA, KB)
        stubs_s = np.repeat(np.arange(Ks), dh)
        tot = len(stubs_s); base = tot // Kb; extra = tot - base * Kb
        assert base + (extra > 0) <= dh
        dgb = np.full(Kb, base); dgb[rng.permutation(Kb)[:extra]] += 1
        stubs_b = rng.permutation(np.repeat(np.arange(Kb), dgb))
        pair = np.stack([stubs_b, stubs_s], axis=1) if big == 0 else np.stack([stubs_s, stubs_b], axis=1)
        he = np.unique(pair, axis=0)
        fp, lst = far_pairs(he, True)
        print(f'hub graph seed {seed}: {len(he)} edges ({len(pair) - len(he)} repeated pairs dropped), {fp} same-side '
              f'(ordered) pairs beyond 6', flush=True)
        rng = np.random.default_rng([seed, 99]); rounds = 0; cap = len(lst)
        while fp > 0:                                      # rounds of disjoint degree-preserving 2-switches, each
            rounds += 1; assert rounds < 400, 'hub graph repair failed'   # aimed at a far pair; kept if fp drops
            E = {(int(a), int(b_)) for a, b_ in he}
            nbr = [dict(), dict()]
            for a, b_ in E:
                nbr[0].setdefault(a, []).append(b_); nbr[1].setdefault(b_, []).append(a)
            touched = [set(), set()]; rem = set(); add = set()
            for t in rng.permutation(len(lst)):
                col, u, w_ = lst[t]                        # u, w_ on side col (0 = line side)
                oc = 1 - col
                if u in touched[col] or w_ in touched[col] or len(add) >= 2 * cap:
                    continue
                pu = nbr[col][u]; p_ = pu[rng.integers(len(pu))]
                y = nbr[col][w_][rng.integers(len(nbr[col][w_]))]
                xs = [z for z in nbr[oc][y] if z not in (u, w_)]
                if not xs:
                    continue
                xx = xs[rng.integers(len(xs))]
                if p_ == y or xx in touched[col] or p_ in touched[oc] or y in touched[oc]:
                    continue
                key = lambda a, b_: (a, b_) if col == 0 else (b_, a)
                e1, e2, n1, n2 = key(u, p_), key(xx, y), key(u, y), key(xx, p_)
                if n1 in E or n2 in E or n1 in add or n2 in add:
                    continue
                rem |= {e1, e2}; add |= {n1, n2}
                touched[col] |= {u, w_, xx}; touched[oc] |= {p_, y}
            he2 = np.array(sorted((E - rem) | add), dtype=np.int64); fp2, lst2 = far_pairs(he2, True)
            if fp2 < fp:
                he, fp, lst = he2, fp2, lst2
            else:
                cap = max(1, cap // 2)                     # smaller batches after a failed round
            print(f'  round {rounds}: {len(add) // 2} switches tried, {fp} far pairs left', flush=True)
    else:
        he = hubE
    assert (he[:, 0] >= 0).all() and (he[:, 0] < KB).all() and (he[:, 1] >= 0).all() and (he[:, 1] < KA).all()
    assert len(np.unique(he, axis=0)) == len(he)
    assert np.bincount(he[:, 0], minlength=KB).max() <= dh and np.bincount(he[:, 1], minlength=KA).max() <= dh
    assert far_pairs(he) == 0, 'hub graph: same-side distance > 6'
    print(f'hub graph: {len(he)} edges, degrees <= {dh}, same-side distances <= 6 on both sides', flush=True)
    if mode == 'make':
        with open(solout, 'w') as f:
            f.write(f'typedherm2 {q} {N} {T} {n}\n')
            if nfdesc == 'multi':
                f.write(f'nonfriendly multi {os.path.basename(nonfr)} {hashlib.sha256(open(nonfr, "rb").read()).hexdigest()}\n')
            else:
                f.write(f'nonfriendly ovoid {len(Rp)}\nR ' + ' '.join(str(t) for t in Rp.tolist()) + '\n')
            f.write(f'hubs {KB} {KA}\nhubgraph {len(he)}\n' + '\n'.join(f'{a} {b_}' for a, b_ in he.tolist()) + '\n')
        print('wrote', solout, flush=True)
    out.append(np.stack([NV0 + he[:, 0], NV0 + KB + he[:, 1]], axis=1).astype(np.int32))
    E = np.concatenate(out); del out
    deg = np.bincount(E.reshape(-1), minlength=n)
    print(f'n = {n}, edges = {len(E)}, degree min {deg.min()} max {deg.max()}, hub graph edges {len(he)}', flush=True)
    assert deg.max() <= Delta
    h = hashlib.sha256()
    with open(outfn, 'w') as f:
        s = '%d\n' % n; f.write(s); h.update(s.encode())
        CH = 1 << 21
        for i in range(0, len(E), CH):
            s = '\n'.join('%d %d' % (u, w_) for u, w_ in E[i:i + CH].tolist()) + '\n'
            f.write(s); h.update(s.encode())
    print('wrote', outfn, 'sha256', h.hexdigest(), flush=True)


if __name__ == '__main__':
    main()

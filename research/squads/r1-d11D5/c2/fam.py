#!/usr/bin/env python3
"""c2 (squad r1-d11D5): chi-twisted H-invariant Z3 cocycles on W(7).

H is given by generators (4x4 matrices over F_7 preserving B(x,y)=x^T J y up to a scalar, J as in the brief).
chi assigns +-1 to each generator.  nu(h f) = chi(h) nu(f) on flags f = (point, line).  Orbit variables are
found by sign-propagation on the Schreier graph (an orbit whose sign monodromy is -1 is forced to 0).
Opposite point pairs / line pairs are reduced to H-orbit representatives (cost is constant on an orbit),
weighted by orbit size, so cost = zcov cost of the expanded labelling.

library: build(name, gens) writes fam_<name>.txt (for c2solve) and fam_<name>.npz (flag var/sign table).
         expand(...) and zcost(...) rebuild the 3200-label file and call zcov SCORE=1 to verify.
"""
import os, sys, struct, subprocess, re, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ZDIR = '/home/user/degree-diameter/research/d11D5/z3'
GQ = ZDIR + '/gq/gq_q7.bin'
Q = 7
K = 8
J = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]], dtype=np.int64)
I4 = np.eye(4, dtype=np.int64)


def load():
    b = open(GQ, 'rb').read()
    q, N, L = struct.unpack('<iii', b[:12])
    assert q == Q and N == 400 and L == 400
    PL = np.frombuffer(b, dtype='<i4', count=L * K, offset=12).reshape(L, K).astype(np.int64)
    co = np.frombuffer(b, dtype=np.uint8, count=N * 7, offset=12 + 4 * L * K).reshape(N, 7).astype(np.int64)
    assert (co[:, 4:] == 0).all()
    return N, L, PL, co[:, :4].copy()


N, L, PL, CO = load()
NF = L * K
FL_LN = np.repeat(np.arange(L), K)
FL_PT = PL.reshape(-1)
FIDX = -np.ones((L, N), dtype=np.int64)
FIDX[FL_LN, FL_PT] = np.arange(NF)
PT_KEY = {tuple(int(x) for x in CO[p]): p for p in range(N)}
LINE_KEY = {frozenset(int(x) for x in PL[l]): l for l in range(L)}
LP = [[] for _ in range(N)]
for l in range(L):
    for p in PL[l]:
        LP[int(p)].append(l)
assert all(len(x) == K for x in LP)
COLL = -np.ones((N, N), dtype=np.int64)   # line joining two collinear points
CONC = -np.ones((L, L), dtype=np.int64)   # point common to two concurrent lines
for l in range(L):
    pts = [int(x) for x in PL[l]]
    for a in pts:
        for b in pts:
            if a != b:
                COLL[a, b] = l
for p in range(N):
    for a in LP[p]:
        for b in LP[p]:
            if a != b:
                CONC[a, b] = p


def inv(a):
    return pow(int(a) % Q, Q - 2, Q)


def normpt(v):
    v = [int(x) % Q for x in v]
    i = next(j for j in range(4) if v[j])
    c = inv(v[i])
    return tuple((x * c) % Q for x in v)


def is_sim(M):
    X = (M.T @ J @ M) % Q
    lam = int(X[0, 1]) % Q
    return lam != 0 and np.array_equal(X, (lam * J) % Q)


def point_perm(M):
    W = (CO @ M.T) % Q
    return np.array([PT_KEY[normpt(w)] for w in W], dtype=np.int64)


def line_perm(pp):
    return np.array([LINE_KEY[frozenset(int(pp[p]) for p in PL[l])] for l in range(L)], dtype=np.int64)


def flag_perm(pp, lpm):
    return FIDX[lpm[FL_LN], pp[FL_PT]]


def solve_flags(items):
    """items: list of (flag perm, chi). Returns var (-1 = forced 0), sig (+-1), nvar."""
    invs = [np.argsort(fp) for fp, _ in items]
    seen = np.zeros(NF, dtype=bool)
    var = -np.ones(NF, dtype=np.int64)
    sig = np.zeros(NF, dtype=np.int64)
    nvar = 0
    for root in range(NF):
        if seen[root]:
            continue
        seen[root] = True
        sg = {root: 1}
        queue = [root]
        ok = True
        qi = 0
        while qi < len(queue):
            f = queue[qi]
            qi += 1
            for (fp, chi), fi in zip(items, invs):
                for nb in (int(fp[f]), int(fi[f])):
                    want = chi * sg[f]
                    if not seen[nb]:
                        seen[nb] = True
                        sg[nb] = want
                        queue.append(nb)
                    elif sg[nb] != want:
                        ok = False
        for f in queue:
            if ok:
                var[f] = nvar
                sig[f] = sg[f]
        if ok:
            nvar += 1
    return var, sig, nvar


def pair_orbits(pt_perms, ln_perms):
    out = []
    for kind, perms in (('p', pt_perms), ('l', ln_perms)):
        if kind == 'p':
            pairs = [(P, Q_) for P in range(N) for Q_ in range(P + 1, N) if COLL[P, Q_] < 0]
            M = N
        else:
            pairs = [(A, B) for A in range(L) for B in range(A + 1, L) if CONC[A, B] < 0]
            M = L
        idx = -np.ones((M, M), dtype=np.int64)
        for i, (a, b) in enumerate(pairs):
            idx[a, b] = i
            idx[b, a] = i
        parent = list(range(len(pairs)))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for pm in perms:
            for i, (a, b) in enumerate(pairs):
                j = int(idx[pm[a], pm[b]])
                assert j >= 0
                ri, rj = find(i), find(j)
                if ri != rj:
                    parent[ri] = rj
        comp = {}
        for i in range(len(pairs)):
            comp.setdefault(find(i), []).append(i)
        out.append([(pairs[lst[0]], len(lst)) for lst in comp.values()])
    return out


def geo_point(P, Q_):
    res = []
    for L1 in LP[P]:
        R = next(int(r) for r in PL[L1] if int(r) != P and COLL[int(r), Q_] >= 0)
        L2 = int(COLL[R, Q_])
        res.append([(P, L1, 1), (R, L1, -1), (R, L2, 1), (Q_, L2, -1)])
    return res


def geo_line(A, B):
    res = []
    for P1 in PL[A]:
        P1 = int(P1)
        K_ = next(l for l in LP[P1] if l != A and CONC[l, B] >= 0)
        P2 = int(CONC[K_, B])
        res.append([(P1, A, -1), (P1, K_, 1), (P2, K_, -1), (P2, B, 1)])
    return res


def build(name, gens, verbose=True):
    """gens: list of (4x4 matrix, chi). Writes fam_<name>.txt and fam_<name>.npz in HERE."""
    pts, lns, items = [], [], []
    for M, chi in gens:
        M = np.array(M, dtype=np.int64) % Q
        assert is_sim(M), 'not a similitude: %s' % name
        pp = point_perm(M)
        lpm = line_perm(pp)
        fp = flag_perm(pp, lpm)
        pts.append(pp)
        lns.append(lpm)
        items.append((fp, chi))
    var, sig, nvar = solve_flags(items)
    porb, lorb = pair_orbits(pts, lns)
    reps = [(wt, geo_point(P, Q_)) for (P, Q_), wt in porb] + [(wt, geo_line(A, B)) for (A, B), wt in lorb]
    txt = os.path.join(HERE, 'fam_%s.txt' % name)
    with open(txt, 'w') as fh:
        fh.write('%d %d\n' % (nvar, len(reps)))
        for wt, geos in reps:
            vals = [wt]
            for g in geos:
                for (pt, ln, s) in g:
                    fl = int(FIDX[ln, pt])
                    v = int(var[fl])
                    c = s * int(sig[fl]) if v >= 0 else 0
                    vals += [max(v, 0), c]
            fh.write(' '.join(map(str, vals)) + '\n')
    np.savez(os.path.join(HERE, 'fam_%s.npz' % name), var=var, sig=sig, nvar=nvar)
    if verbose:
        print('build %-22s nvar=%4d  pair-orbit reps=%6d (point %d, line %d)  forced-zero flags=%d' % (
            name, nvar, len(reps), len(porb), len(lorb), int((var < 0).sum())), flush=True)
    return nvar, len(reps)


def expand(name, x):
    d = np.load(os.path.join(HERE, 'fam_%s.npz' % name))
    var, sig = d['var'], d['sig']
    lab = np.zeros(NF, dtype=np.int64)
    m = var >= 0
    xa = np.asarray(x, dtype=np.int64)
    lab[m] = (sig[m] * xa[var[m]]) % 3
    return lab


def zcost(lab, path):
    with open(path, 'w') as fh:
        fh.write('\n'.join(str(int(v)) for v in lab) + '\n')
    env = dict(os.environ, SCORE='1', IN=path)
    out = subprocess.run(['./zcov', '7', '3'], cwd=ZDIR, env=env, capture_output=True, text=True, timeout=600).stdout
    m = re.search(r'cost=(\d+)', out)
    return int(m.group(1)), out.strip()


def solve(name, mode, secs, seed, outc, T=None):
    cmd = [os.path.join(HERE, 'c2solve'), os.path.join(HERE, 'fam_%s.txt' % name), str(mode), str(secs),
           str(seed), outc]
    if T:
        cmd += [str(T[0]), str(T[1])]
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=900).stdout
    m = re.search(r'k=(\d+) nrep=(\d+) best=(\d+) iters=(\d+) mode=(\d+)', out)
    x = [int(v) for v in open(outc).read().split()] if os.path.exists(outc) else []
    return int(m.group(3)), int(m.group(4)), x, out.strip()


# ---- group generators -------------------------------------------------------------------------------
U2 = np.array([[1, 1], [0, 1]])
W2 = np.array([[0, 1], [6, 0]])   # [[0,1],[-1,0]]
D2 = np.array([[3, 0], [0, 5]])   # diag(a, a^-1), a = 3


def blk1(A2):
    M = np.eye(4, dtype=np.int64)
    M[0:2, 0:2] = A2
    return M


def blk2(A2):
    M = np.eye(4, dtype=np.int64)
    M[2:4, 2:4] = A2
    return M


def diag2(A2):
    M = np.zeros((4, 4), dtype=np.int64)
    M[0:2, 0:2] = A2
    M[2:4, 2:4] = A2
    return M


S_SWAP = np.array([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]], dtype=np.int64)


def order_of(A2, maxo=100):
    M = A2.copy() % Q
    for o in range(1, maxo + 1):
        if np.array_equal(M, np.eye(2, dtype=np.int64)):
            return o
        M = (M @ A2) % Q
    return None


def nonsplit_A8():
    for s in range(7):
        A = np.array([[0, 1], [6, s]], dtype=np.int64)
        if order_of(A) == 8:
            return A
    raise RuntimeError('no order-8 element')


def mat_order(g, maxo=200):
    M = g.copy() % Q
    for o in range(1, maxo + 1):
        if np.array_equal(M, I4):
            return o
        M = (M @ g) % Q
    return None


def rand_transvection_product(rng, nfac=8):
    g = I4.copy()
    for _ in range(nfac):
        v = np.array([rng.randrange(Q) for _ in range(4)], dtype=np.int64).reshape(4, 1)
        t = rng.randrange(1, Q)
        T = (I4 - t * (v @ v.T) @ J) % Q
        assert is_sim(T)
        g = (g @ T) % Q
    return g


def find_singer(rng, want=50):
    for _ in range(200000):
        g = rand_transvection_product(rng)
        if mat_order(g, want + 1) == want:
            return g
    raise RuntimeError('no element of order %d found' % want)


def sylow7(rng):
    """Upper unitriangular symplectic matrices in the adapted basis (e0, e2, e3, e1)."""
    P = np.array([[1, 0, 0, 0], [0, 0, 0, 1], [0, 1, 0, 0], [0, 0, 1, 0]], dtype=np.int64)
    pos = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    import itertools
    els = []
    for vals in itertools.product(range(Q), repeat=6):
        Mb = I4.copy()
        for (i, j), v in zip(pos, vals):
            Mb[i, j] = v
        M = (P @ Mb @ P.T) % Q
        if np.array_equal((M.T @ J @ M) % Q, J % Q):
            els.append(M)
    assert len(els) == Q ** 4, len(els)
    # pick generators until the closure is the whole group
    def closure(gs, cap=3000):
        seen = {I4.tobytes()}
        frontier = [I4]
        while frontier:
            nf = []
            for x in frontier:
                for g in gs:
                    y = (x @ g) % Q
                    kb = y.tobytes()
                    if kb not in seen:
                        seen.add(kb)
                        nf.append(y)
                        if len(seen) > cap:
                            return None
            frontier = nf
        return len(seen)
    gens = []
    while True:
        gens.append(els[rng.randrange(len(els))])
        if closure(gens) == Q ** 4:
            return gens


def main_families(which=None, secs=10.0, exh_limit=1.5e10, seed=1):
    import random
    rng = random.Random(seed)
    results = []
    A8 = nonsplit_A8()
    # torus C6xC6 (split torus of SL2 x SL2), chi twists
    fams = {}
    for c1 in (1, -1):
        for c2 in (1, -1):
            fams['T36_%+d%+d' % (c1, c2)] = [(blk1(D2), c1), (blk2(D2), c2)]
    for c1 in (1, -1):
        for c2 in (1, -1):
            fams['C8xC8_%+d%+d' % (c1, c2)] = [(blk1(A8), c1), (blk2(A8), c2)]
    for c1 in (1, -1):
        for c2 in (1, -1):
            for c3 in (1, -1):
                fams['C8xC8S_%+d%+d%+d' % (c1, c2, c3)] = [(blk1(A8), c1), (blk2(A8), c2), (S_SWAP, c3)]
    for c1 in (1, -1):
        for c2 in (1, -1):
            for c3 in (1, -1):
                fams['NT288_%+d%+d%+d' % (c1, c2, c3)] = [(blk1(D2), c1), (blk1(W2), c2), (S_SWAP, c3)]
    for c1 in (1, -1):
        fams['C8_%+d' % c1] = [(blk1(A8), c1)]
    fams['S2_+1'] = [(S_SWAP, 1)]
    fams['SL2_1x'] = [(blk1(U2), 1), (blk1(W2), 1)]
    fams['DSL2'] = [(diag2(U2), 1), (diag2(W2), 1)]
    singer = find_singer(rng, 50)
    fams['Singer50'] = [(singer, 1)]
    sy = sylow7(rng)
    fams['Sylow7'] = [(g, 1) for g in sy]
    rows = []
    for name, gens in fams.items():
        if which and name not in which:
            continue
        nvar, nrep = build(name, gens)
        best = None
        if math.log(2) + max(nvar - 1, 0) * math.log(3) + math.log(nrep * 32) <= math.log(exh_limit):
            mode, tsec = 0, 0
        else:
            mode, tsec = 1, secs
        b, its, x, raw = solve(name, mode, tsec, seed, os.path.join(HERE, 'best_%s.txt' % name))
        lab = expand(name, x)
        cz, zout = zcost(lab, os.path.join(HERE, 'labels_%s.txt' % name))
        mode_s = 'exh' if mode == 0 else 'anneal'
        print('  %-18s mode=%-6s solver_best=%d zcov_cost=%d  (%s)' % (name, mode_s, b, cz, raw), flush=True)
        rows.append((name, nvar, nrep, mode_s, b, cz))
    return rows


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--only', nargs='*')
    ap.add_argument('--secs', type=float, default=10.0)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    rows = main_families(a.only, a.secs, seed=a.seed)
    print('SUMMARY')
    for r in sorted(rows, key=lambda r: r[5]):
        print(r)

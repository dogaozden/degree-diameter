#!/usr/bin/env python3
"""Card c1, squad round d7thm-r1 (thm-conics).

Builds the split Cayley hexagon H(q) for an odd prime q from the quadric
X0X4 + X1X5 + X2X6 - X3^2 and Tits' Pluecker equations (written independently
here, not taken from hexgen2.c), then checks the claims of the brief for the
odd-q sets.  Usage:  python3 hex_check.py 3 5 7
"""
import sys
import time
import json
import itertools
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path

T0 = time.time()
QS = [int(a) for a in sys.argv[1:]] or [3, 5, 7]
ALL_RESULTS = {}


def run(q):
    res = {}          # item -> (pass, detail)
    info = {}         # numbers for the report

    def log(*a):
        print(f"[{time.time()-T0:7.1f}s] q={q}", *a, flush=True)

    def record(item, ok, detail):
        res[item] = (bool(ok), detail)
        log(f"item {item}: {'PASS' if ok else 'FAIL'} :: {detail}")

    assert q % 2 == 1 and q > 2
    INV = np.zeros(q, dtype=np.int64)
    for a in range(1, q):
        INV[a] = pow(a, q - 2, q)
    PW = q ** np.arange(7, dtype=np.int64)

    # ------------------------------------------------------------------
    # Points: normalized X in F^7 with Q(X)=0, Q = X0X4 + X1X5 + X2X6 - X3^2
    # ------------------------------------------------------------------
    idx = np.arange(q ** 7, dtype=np.int64)
    D = (idx[:, None] // PW[None, :]) % q          # digit i = coordinate X_i
    nzm = D != 0
    has = nzm.any(1)
    first = nzm.argmax(1)
    lead = D[idx, first]
    normal = has & (lead == 1)
    Qv = (D[:, 0] * D[:, 4] + D[:, 1] * D[:, 5] + D[:, 2] * D[:, 6] - D[:, 3] * D[:, 3]) % q
    pts = D[normal & (Qv == 0)]
    del D, idx, nzm, has, first, lead, normal, Qv
    N = len(pts)
    assert N == (q ** 6 - 1) // (q - 1), N
    keyToId = -np.ones(q ** 7, dtype=np.int64)
    keyToId[pts @ PW] = np.arange(N)

    def normalize(V):
        f = (V != 0).argmax(1)
        ld = V[np.arange(len(V)), f]
        return (V * INV[ld][:, None]) % q

    def pid(V):
        return keyToId[normalize(V) @ PW]

    def nullspace_mod(A):
        A = [list(r) for r in A]
        m, n = len(A), len(A[0])
        piv = []
        r = 0
        for c in range(n):
            pr = None
            for i in range(r, m):
                if A[i][c] % q:
                    pr = i
                    break
            if pr is None:
                continue
            A[r], A[pr] = A[pr], A[r]
            iv = pow(A[r][c], q - 2, q)
            A[r] = [(v * iv) % q for v in A[r]]
            for i in range(m):
                if i != r and A[i][c] % q:
                    f = A[i][c]
                    A[i] = [(A[i][j] - f * A[r][j]) % q for j in range(n)]
            piv.append(c)
            r += 1
            if r == m:
                break
        basis = []
        for fc in [c for c in range(n) if c not in piv]:
            v = [0] * n
            v[fc] = 1
            for i, pc in enumerate(piv):
                v[pc] = (-A[i][fc]) % q
            basis.append(v)
        return basis

    def rank_mod(M):
        return q_rank(M)

    def q_rank(M):
        M = [list(r) for r in M]
        m, n = len(M), len(M[0])
        r = 0
        for c in range(n):
            pr = None
            for i in range(r, m):
                if M[i][c] % q:
                    pr = i
                    break
            if pr is None:
                continue
            M[r], M[pr] = M[pr], M[r]
            iv = pow(M[r][c], q - 2, q)
            M[r] = [(v * iv) % q for v in M[r]]
            for i in range(m):
                if i != r and M[i][c] % q:
                    f = M[i][c]
                    M[i] = [(M[i][j] - f * M[r][j]) % q for j in range(n)]
            r += 1
        return r

    # ------------------------------------------------------------------
    # Lines.  Plucker p_ab(x,y) = x_a y_b - x_b y_a.  Six equations
    # p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.  With B the polar
    # form, lines through x are <x,y> with y in the kernel K_x of the
    # 7 linear forms (6 Pluecker equations, B(x,.)).
    # ------------------------------------------------------------------
    EQS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
           ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]

    def eq_matrix(x):
        A = np.zeros((7, 7), dtype=np.int64)
        for k, ((a, b), (c, d)) in enumerate(EQS):
            A[k, b] += x[a]
            A[k, a] -= x[b]
            A[k, d] -= x[c]
            A[k, c] += x[d]
        A[6] = [x[4], x[5], x[6], -2 * x[3], x[0], x[1], x[2]]
        return A % q

    # normalized coefficient triples for a plane (projective 2-space of coefficients)
    C3 = [(1, s, t) for s in range(q) for t in range(q)] + [(0, 1, t) for t in range(q)] + [(0, 0, 1)]
    C3 = np.array(C3, dtype=np.int64)
    assert len(C3) == q * q + q + 1

    t_arr = np.arange(q, dtype=np.int64)
    rows = []
    plane_ok = True
    for xi in range(N):
        x = pts[xi]
        basis = nullspace_mod(eq_matrix(x).tolist())
        if len(basis) != 3:
            plane_ok = False
            break
        Bm = np.array(basis, dtype=np.int64)
        ids = pid((C3 @ Bm) % q)
        if (ids < 0).any() or len(set(ids.tolist())) != q * q + q + 1 or xi not in ids:
            plane_ok = False
            break
        ys = pts[ids[ids != xi]]
        combos = (x[None, None, :] + t_arr[:, None, None] * ys[None, :, :]) % q
        allc = np.concatenate([combos, ys[None]], axis=0).reshape(-1, 7)
        lid = pid(allc).reshape(q + 1, -1).T
        lid.sort(axis=1)
        rows.append(lid)
    LP = np.unique(np.concatenate(rows), axis=0)
    del rows
    L = len(LP)
    ownerL = np.repeat(np.arange(L), q + 1)
    flatP = LP.ravel()
    PL = ownerL[np.argsort(flatP, kind="stable")].reshape(N, q + 1)
    pcount = np.bincount(flatP, minlength=N)
    lcount_ok = bool((pcount == q + 1).all()) and bool((np.diff(LP, axis=1) > 0).all())   # rows strictly increasing = q+1 distinct points

    # Plucker equations on each line (from two of its points)
    u = pts[LP[:, 0]]
    w = pts[LP[:, 1]]

    def pf(a, b):
        return (u[:, a] * w[:, b] - u[:, b] * w[:, a]) % q
    plu_ok = all(((pf(a, b) - pf(c, d)) % q == 0).all() for ((a, b), (c, d)) in EQS)
    Qline = all(((pts[LP[:, j], 0] * pts[LP[:, j], 4] + pts[LP[:, j], 1] * pts[LP[:, j], 5]
                  + pts[LP[:, j], 2] * pts[LP[:, j], 6] - pts[LP[:, j], 3] ** 2) % q == 0).all()
                for j in range(q + 1))

    # incidence graph: vertices 0..N-1 points, N..N+L-1 lines
    rr = np.concatenate([flatP, N + ownerL])
    cc = np.concatenate([N + ownerL, flatP])
    Gr = csr_matrix((np.ones(len(rr)), (rr, cc)), shape=(N + L, N + L))

    def dist_from(srcs):
        srcs = np.atleast_1d(np.asarray(srcs))
        out = np.empty((len(srcs), N + L))
        for s in range(0, len(srcs), 256):
            out[s:s + 256] = shortest_path(Gr, directed=False, unweighted=True, indices=srcs[s:s + 256])
        return out

    # sanity: distance-level sizes from points and from lines (GH(q,q))
    expect = [1, q + 1] + [(q + 1) * q ** (k - 1) for k in range(2, 6)] + [q ** 5]
    samp = list(range(N + L)) if q == 3 else list(range(0, N + L, max(1, (N + L) // 300)))
    dsamp = dist_from(samp)
    lev_ok = True
    for row in dsamp:
        cnt = np.bincount(row.astype(int), minlength=7)
        if cnt.tolist() != expect:
            lev_ok = False
            break
    diam_ok = bool(dsamp.max() == 6)
    log(f"graph: N={N} points, L={L} lines, sanity sources={len(samp)}, level sizes {expect} ok={lev_ok}")

    ncheck1 = dict(N=N, L=L, plane=plane_ok, lines_per_pt=lcount_ok, plucker=plu_ok, on_quadric=Qline,
                   levels=lev_ok, diam6=diam_ok)
    info["item1"] = ncheck1
    item1 = (N == (q ** 6 - 1) // (q - 1) and L == N and plane_ok and lcount_ok and plu_ok and Qline
             and lev_ok and diam_ok)
    record(1, item1, f"N={N} points, L={L} lines, q+1={q+1} pts/line, each point on q+1 lines (ok={lcount_ok}); "
           f"Pluecker eqs ok={plu_ok}; diam6/level-size sanity ok={lev_ok and diam_ok} over {len(samp)} sources")

    # ------------------------------------------------------------------
    # c, (c0,c1), Pi, S, P_S, v, L_v, free points
    # ------------------------------------------------------------------
    sq = {(a * a) % q for a in range(1, q)}
    nonsq = [a for a in range(1, q) if a not in sq]
    c = next(cc_ for cc_ in range(1, q) if (-cc_) % q in nonsq)

    def Gf(a, b, c0, c1):
        return ((c0 * a + c1 * b) * (a * a + c * b * b) - b ** 3) % q

    zf = []
    for c0 in range(q):
        for c1 in range(q):
            if all(Gf(a, b, c0, c1) != 0 for a in range(q) for b in range(q) if (a, b) != (0, 0)):
                zf.append((c0, c1))
    c0, c1 = zf[0]
    info["c"] = c
    info["c0c1"] = [c0, c1]
    info["n_zero_free_c0c1"] = len(zf)

    X0, X2, X3, X4, X5, X6 = pts[:, 0], pts[:, 2], pts[:, 3], pts[:, 4], pts[:, 5], pts[:, 6]
    f0 = (pts[:, 0] + c * pts[:, 4]) % q
    Pi_pt = f0 == 0
    Smask = (f0[LP] == 0).all(1)
    S_ids = np.nonzero(Smask)[0]
    assert len(S_ids) == q ** 3 + 1, len(S_ids)
    e1 = keyToId[(np.array([0, 1, 0, 0, 0, 0, 0]) @ PW)]
    e6 = keyToId[(np.array([0, 0, 0, 0, 0, 0, 1]) @ PW)]
    vs = sorted(set(PL[e1].tolist()) & set(PL[e6].tolist()))
    assert len(vs) == 1
    vid = vs[0]
    Lidx = np.arange(L)
    Vmask = Lidx == vid

    dist_v = dist_from([N + vid])[0]          # distances from v to all vertices
    dv_pt = dist_v[:N].astype(int)
    dv_ln = dist_v[N:].astype(int)
    D_S = dist_from(N + S_ids)[:, N + S_ids]
    S_opp = bool(((D_S == 6) | np.eye(len(S_ids), dtype=bool)).all())

    PS_pt = np.zeros(N, dtype=bool)
    PS_pt[LP[S_ids].ravel()] = True
    psl = -np.ones(N, dtype=np.int64)
    for s in S_ids:
        psl[LP[s]] = s
    Lv_ids = np.nonzero(dv_ln == 2)[0]
    near_pts = dv_pt <= 3
    near_expected = (X2 == 0) & (X5 == 0)
    free = (~Pi_pt) & (dv_pt == 5)
    info["counts"] = dict(S=len(S_ids), PS=int(PS_pt.sum()), Lv=len(Lv_ids), near3=int(near_pts.sum()),
                          free=int(free.sum()))

    item2 = (S_opp and len(S_ids) == q ** 3 + 1 and bool(Smask[vid])
             and bool(np.array_equal(PS_pt, Pi_pt)) and int(PS_pt.sum()) == (q + 1) * (q ** 3 + 1)
             and len(Lv_ids) == q * (q + 1) and bool(np.array_equal(near_pts, near_expected))
             and int(free.sum()) == q ** 3 * (q * q - 1)
             and bool(Pi_pt[e1] and Pi_pt[e6]))
    record(2, item2,
           f"|S|={len(S_ids)} (q^3+1) pairwise opposite={S_opp}; |P_S|={int(PS_pt.sum())} "
           f"(=(q+1)(q^3+1)={(q+1)*(q**3+1)}), P_S==points in Pi: {bool(np.array_equal(PS_pt, Pi_pt))}; "
           f"|L_v|={len(Lv_ids)} (q(q+1)={q*(q+1)}); #points at dist<=3 from v={int(near_pts.sum())}, "
           f"==(X2=X5=0): {bool(np.array_equal(near_pts, near_expected))}; "
           f"#free={int(free.sum())} (q^3(q^2-1)={q**3*(q*q-1)})")

    # ------------------------------------------------------------------
    # nu, W
    # ------------------------------------------------------------------
    den = (c * X2 * X2 + X5 * X5) % q
    numr = (X2 * X3 - X4 * X5) % q
    nu = -np.ones(N, dtype=np.int64)
    okn = den != 0
    nu[okn] = (numr[okn] * INV[den[okn]]) % q

    def build_W(c0, c1):
        W_all = []
        onv_excluded = 0
        for al in range(q):
            for be in range(q):
                if al == 0 and be == 0:
                    continue
                fz = (f0 + al * X2 + be * X5) % q
                Sz = (fz[LP] == 0).all(1)
                cand = np.nonzero(Sz & ~Smask)[0]
                if len(cand) == 0:
                    continue
                P0 = (f0[LP[cand]] == 0)
                assert (P0.sum(1) == 1).all()
                Xs = LP[cand][np.arange(len(cand)), P0.argmax(1)]
                onv = (X2[Xs] == 0) & (X5[Xs] == 0)
                onv_excluded += int(onv.sum())
                Fz = (Gf(al, be, c0, c1) * INV[(al * al + c * be * be) % q]) % q
                keep = ~onv
                sel = cand[keep][nu[Xs[keep]] == Fz]
                W_all.extend(sel.tolist())
        return np.array(sorted(W_all), dtype=np.int64), W_all, onv_excluded

    W, W_all, onv_excluded = build_W(c0, c1)
    W_distinct = len(set(W_all)) == len(W_all)
    wcount = np.bincount(LP[W].ravel(), minlength=N)
    info["W"] = len(W)
    info["onv_excluded"] = onv_excluded
    # robustness: the same W-claims for every zero-free (c0,c1) pair
    rob = []
    for (d0, d1) in zf:
        Wd, _, _ = build_W(d0, d1)
        wcd = np.bincount(LP[Wd].ravel(), minlength=N)
        rob.append(len(Wd) == q * q * (q * q - 1) and bool((wcd[free] == 1).all()))
    info["W_robust_all_zero_free_pairs"] = [len(zf), all(rob)]

    item3 = (len(W) == q * q * (q * q - 1) and W_distinct
             and bool((dv_ln[W] == 6).all()) and not Smask[W].any()
             and bool((wcount[free] == 1).all()))
    record(3, item3,
           f"|W|={len(W)} (q^2(q^2-1)={q*q*(q*q-1)}), distinct={W_distinct}; "
           f"all W lines opposite v={bool((dv_ln[W] == 6).all())}, none in S={not Smask[W].any()}; "
           f"free points with exactly one W-line: {int((wcount[free] == 1).sum())}/{int(free.sum())}, "
           f"max W-lines per free point={int(wcount[free].max())}; W-lines on v-meeting cand. excluded={onv_excluded}; "
           f"same claims for all {len(zf)} zero-free (c0,c1) pairs: {all(rob)}")

    # ------------------------------------------------------------------
    # Item 4: nu on S lines, W-meeting counts
    # ------------------------------------------------------------------
    Sot = S_ids[S_ids != vid]
    nuL = nu[LP[Sot]]
    nu_const = bool((nuL == nuL[:, :1]).all() and (nuL >= 0).all())
    wc_m = wcount[LP[Sot]]
    cnt_m = wc_m.sum(1)
    cnt_ok = bool(np.isin(cnt_m, [0, q + 1]).all())
    one_each = bool(((cnt_m != q + 1) | (wc_m == 1).all(1)).all())
    S0 = Sot[cnt_m == 0]
    nu0 = Sot[nuL[:, 0] == 0]
    info["nu_dist_on_S"] = {int(k): int(v) for k, v in zip(*np.unique(nuL[:, 0], return_counts=True))}
    info["meet_counts"] = {int(k): int(v) for k, v in zip(*np.unique(cnt_m, return_counts=True))}
    item4 = nu_const and cnt_ok and one_each and len(S0) == q * q and set(S0.tolist()) == set(nu0.tolist())
    record(4, item4,
           f"nu constant on each S-line != v: {nu_const}; W-meet counts {info['meet_counts']} "
           f"(one per point when q+1: {one_each}); |S_0|={len(S0)} (q^2={q*q}); "
           f"S_0 == {{nu=0}}: {set(S0.tolist()) == set(nu0.tolist())} (|nu=0|={len(nu0)})")

    # ------------------------------------------------------------------
    # Item 5: R_L = L_v + W + S_0 dual segment set, maximal, covers points
    # ------------------------------------------------------------------
    RL_ids = np.concatenate([Lv_ids, W, S0])
    RL_mask = np.zeros(L, dtype=bool)
    RL_mask[RL_ids] = True

    def dual_literal(Gm):
        G_ids = np.nonzero(Gm)[0]
        for l in G_ids:
            hit = 0
            for p in LP[l]:
                others = PL[p][Gm[PL[p]] & (PL[p] != l)]
                if len(others):
                    hit += 1
            if hit > 1:
                return False
        return True

    def dual_fast_after_add(Gm, m):
        """True if Gm + {m} is still a dual segment set (vectorized, same criterion:
        for each line l of the set, #points p on l lying on another line of the set <= 1)."""
        G2 = Gm.copy()
        G2[m] = True
        G2_ids = np.nonzero(G2)[0]
        cp2 = np.bincount(LP[G2_ids].ravel(), minlength=N)
        H = (cp2[LP[G2_ids]] >= 2).sum(1)
        return not bool((H > 1).any())

    rl_dual = dual_literal(RL_mask)
    cover = bool((np.bincount(LP[RL_ids].ravel(), minlength=N) >= 1).all())
    cand_out = np.nonzero(~RL_mask)[0]
    survive_fast = 0
    survive_vec = []
    for m in cand_out:
        if dual_fast_after_add(RL_mask, m):
            survive_fast += 1
            survive_vec.append(int(m))
    survive = survive_fast
    cross = None
    if q <= 5:   # literal check of every candidate, to cross-validate the fast criterion
        lit = []
        for m in cand_out:
            G2 = RL_mask.copy()
            G2[m] = True
            if dual_literal(G2):
                lit.append(int(m))
        cross = (lit == survive_vec)
    maximal = survive == 0
    info["RL"] = len(RL_ids)
    info["RL_survive_adding"] = survive
    info["RL_cross_check_literal"] = cross
    item5 = (len(RL_ids) == len(set(RL_ids.tolist())) and len(RL_ids) == q ** 4 + q * q + q and rl_dual
             and cover and maximal and (cross is None or cross))
    record(5, item5,
           f"|R_L|={len(RL_ids)} (q^4+q^2+q={q**4+q*q+q}), distinct={len(RL_ids)==len(set(RL_ids.tolist()))}; "
           f"dual segment set (literal)={rl_dual}; every point covered={cover}; "
           f"lines outside R_L keeping dual-segment property: {survive}/{len(cand_out)} "
           f"(literal cross-check: {cross})")

    # ------------------------------------------------------------------
    # Item 6: R_H = P_S segment set; negative controls
    # ------------------------------------------------------------------
    def seg_literal(Fm):
        F_ids = np.nonzero(Fm)[0]
        cl = Fm[LP].sum(1)
        for p in F_ids:
            k = int((cl[PL[p]] >= 2).sum())
            if k > 1:
                return False
        return True

    def seg_fast_after_add(Fm, x):
        """True if Fm + {x} is still a segment set (vectorized version of seg_literal)."""
        cl2 = Fm[LP].sum(1)
        cl2[PL[x]] += 1
        F2_ids = np.append(np.nonzero(Fm)[0], x)
        K = (cl2[PL[F2_ids]] >= 2).sum(1)
        return bool((K <= 1).all())

    ps_seg = seg_literal(PS_pt)
    ps_size = int(PS_pt.sum()) == (q + 1) * (q ** 3 + 1)
    out_pts = np.nonzero(~PS_pt)[0]
    ps_surv = [int(x) for x in out_pts if seg_fast_after_add(PS_pt, x)]
    ps_cross = None
    if q <= 5:
        lit = [int(x) for x in out_pts if seg_literal(np.logical_or(PS_pt, np.arange(N) == x))]
        ps_cross = (lit == ps_surv)
    item6 = ps_seg and ps_size and len(ps_surv) == 0 and (ps_cross is None or ps_cross)
    record(6, item6,
           f"P_S segment set (literal)={ps_seg}, |P_S|={int(PS_pt.sum())}; points x outside P_S with P_S+x still a "
           f"segment set: {len(ps_surv)}/{len(out_pts)} (literal cross-check: {ps_cross}); "
           f"R_L + one line still dual segment set: {survive}/{len(cand_out)}")

    # ------------------------------------------------------------------
    # Item 7: elliptic quadric section of a 3-space, pairwise opposite points
    # ------------------------------------------------------------------
    rng = np.random.default_rng(20261029 + q)
    proj4 = np.array([t for t in itertools.product(range(q), repeat=4)
                      if any(t) and t[next(i for i in range(4) if t[i])] == 1], dtype=np.int64)
    found = None
    tries = 0
    while found is None and tries < 5000:
        tries += 1
        R = rng.integers(0, q, size=(4, 7))
        if q_rank(R.tolist()) < 4:
            continue
        Vn = normalize((proj4 @ R) % q)
        zero = ((Vn[:, 0] * Vn[:, 4] + Vn[:, 1] * Vn[:, 5] + Vn[:, 2] * Vn[:, 6] - Vn[:, 3] ** 2) % q) == 0
        Z = Vn[zero]
        if len(Z) != q * q + 1:
            continue
        Zset = set((Z @ PW).tolist())
        has_line = False
        for i in range(len(Z)):
            for j in range(i + 1, len(Z)):
                ok_line = True
                for t in range(q):
                    pt_ = normalize(((Z[i] + t * Z[j]) % q)[None, :])[0]
                    if int(pt_ @ PW) not in Zset:
                        ok_line = False
                        break
                if ok_line:
                    has_line = True
                    break
            if has_line:
                break
        if not has_line:
            found = Z
    if found is None:
        record(7, False, "no elliptic 3-space found")
        item7 = False
    else:
        Zids = pid(found)
        assert (Zids >= 0).all()
        DZ = dist_from(Zids)[:, Zids]
        opp = bool(((DZ == 6) | np.eye(len(Zids), dtype=bool)).all())
        info["elliptic_tries"] = tries
        item7 = opp and len(Zids) == q * q + 1
        record(7, item7, f"found Sigma after {tries} random 4-spaces; Sigma cap Q has {len(Zids)} points "
               f"(q^2+1={q*q+1}), no line inside; pairwise distance 6 in H(q): {opp}")

    # ---- self-test of the literal / fast checkers: they must accept a star and reject a bad set ----
    p0 = int(LP[0][0])
    star_lines = [int(l) for l in PL[p0]]
    Gs = np.zeros(L, dtype=bool)
    Gs[star_lines] = True
    l1, l2 = star_lines[0], star_lines[1]
    a_pt = int([p for p in LP[l1] if p != p0][0])
    m_bad = [int(l) for l in PL[a_pt] if l != l1][0]
    Gb = Gs.copy()
    Gb[m_bad] = True
    b_pt = int([p for p in LP[l2] if p != p0][0])
    F0 = np.zeros(N, dtype=bool)
    F0[[p0, a_pt]] = True
    Fb = F0.copy()
    Fb[b_pt] = True
    selftest = dict(star_is_dual=dual_literal(Gs), star_plus_bad_line_rejected=not dual_literal(Gb),
                    fast_rejects_bad_line=not dual_fast_after_add(Gs, m_bad),
                    two_branch_point_set_rejected=not seg_literal(Fb),
                    fast_rejects_two_branch=not seg_fast_after_add(F0, b_pt),
                    line_pair_is_segment=seg_literal(F0))
    info["selftest"] = selftest
    log("selftest", selftest)
    passed = sum(1 for k in res if res[k][0])
    log(f"SUMMARY q={q}: passed {passed}/7   info={json.dumps(info, default=str)}")
    return {"q": q, "passed": passed, "items": {str(k): {"pass": v[0], "detail": v[1]} for k, v in res.items()},
            "info": info}


if __name__ == "__main__":
    out = []
    for q in QS:
        out.append(run(q))
        with open(f"/home/user/degree-diameter/research/squads/d7thm-r1/c1/results_q{q}.json", "w") as fh:
            json.dump(out[-1], fh, indent=1, default=str)
    total = sum(r["passed"] for r in out)
    print(f"TOTAL passed {total} of {7*len(out)} (q={QS})", flush=True)

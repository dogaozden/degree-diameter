#!/usr/bin/env python3
"""c5 (squad r3-d8): structure statistics of optimized H(q) lifts vs random lifts.

Lift format: liftdiam file (NB M1 M2 E; flags first, then hop matching 1, then hop matching 2).
Gauge: BFS spanning tree of the flag incidence graph, potentials phi with tree flags = 0; the gauged
dart voltage is w + phi(head) - phi(tail).  Statistics are computed on the gauged lift.
usage: c5_stats.py NSAMPLE SEED   (prints a table; writes results.json next to this file)
"""
import os, sys, json, time
from collections import deque
import numpy as np

QOF = {63: 2, 364: 3, 1365: 4}
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = '/home/user/degree-diameter'


class Grp:
    def __init__(self, M1, M2):
        self.M1, self.M2, self.M = M1, M2, M1 * M2
        g = np.arange(self.M); g1, g2 = g // M2, g % M2
        self.ADD = ((g1[:, None] + g1[None, :]) % M1) * M2 + (g2[:, None] + g2[None, :]) % M2
        self.NEG = ((-g1) % M1) * M2 + ((-g2) % M2)
        self.SUB = self.ADD[:, self.NEG]          # SUB[x, y] = x - y
    def enc(self, a, b):
        return (np.asarray(a) % self.M1) * self.M2 + (np.asarray(b) % self.M2)


def load_file(path):
    with open(path) as fh:
        NB, M1, M2, E = map(int, fh.readline().split())
        rows = np.loadtxt(fh, dtype=np.int64, ndmin=2)
    N = NB // 2; q = QOF[N]; F = (q + 1) * N; j = (E - F) // N
    assert rows.shape == (E, 4) and F + j * N == E and NB == 2 * N
    return dict(q=q, N=N, M1=M1, M2=M2, j=j, rows=rows, F=F)


def structure(rows, N, F, j, grp):
    fr = rows[:F]
    assert (fr[:, 0] < N).all() and (fr[:, 1] >= N).all()
    Pf = fr[:, 0].copy(); Lf = fr[:, 1] - N; Wf = grp.enc(fr[:, 2], fr[:, 3])
    HL, HW = [], []
    for k in range(j):
        blk = rows[F + k * N: F + (k + 1) * N]
        isp = blk[:, 0] < N
        assert np.where(isp, blk[:, 1] >= N, blk[:, 0] >= N).all()
        pts = np.where(isp, blk[:, 0], blk[:, 1])
        lines = np.where(isp, blk[:, 1], blk[:, 0]) - N
        sa = np.where(isp, blk[:, 2], -blk[:, 2]); sb = np.where(isp, blk[:, 3], -blk[:, 3])
        assert np.array_equal(np.sort(pts), np.arange(N)), 'hop block is not a perfect matching'
        hl = np.empty(N, np.int64); hw = np.empty(N, np.int64)
        hl[pts] = lines; hw[pts] = grp.enc(sa, sb)
        HL.append(hl); HW.append(hw)
    return Pf, Lf, Wf, HL, HW


def gauge(N, Pf, Lf, Wf, HL, HW, grp):
    V2 = 2 * N
    adj = [[] for _ in range(V2)]
    for p, l, w in zip(Pf.tolist(), Lf.tolist(), Wf.tolist()):
        adj[p].append((N + l, w)); adj[N + l].append((p, int(grp.NEG[w])))
    phi = np.full(V2, -1, np.int64); phi[0] = 0
    dq = deque([0])
    while dq:
        x = dq.popleft()
        for y, w in adj[x]:
            if phi[y] < 0:
                phi[y] = grp.SUB[phi[x], w]; dq.append(y)
    assert (phi >= 0).all()
    Wg = grp.ADD[Wf, grp.SUB[phi[N + Lf], phi[Pf]]]
    pts = np.arange(N)
    Tg = [grp.ADD[hw, grp.SUB[phi[N + hl], phi[pts]]] for hl, hw in zip(HL, HW)]
    return Wg, Tg


def flag_distances(N, Pf, Lf):
    V2 = 2 * N
    A = np.zeros((V2, V2), np.float32)
    A[Pf, N + Lf] = 1; A[N + Lf, Pf] = 1
    Dm = np.full((V2, V2), 127, np.int16)
    seen = np.eye(V2, dtype=bool); Dm[seen] = 0
    front = seen.astype(np.float32)
    for d in range(1, 13):
        nxt = ((front @ A) > 0) & ~seen
        if not nxt.any():
            break
        Dm[nxt] = d; seen |= nxt; front = nxt.astype(np.float32)
    assert (Dm < 127).all()
    return Dm


def geometry(N, q, Pf, Lf, Dm):
    lines_of_pt = Lf[np.argsort(Pf, kind='stable')].reshape(N, q + 1)
    pts_of_line = Pf[np.argsort(Lf, kind='stable')].reshape(N, q + 1)
    # generalized hexagon sanity: diameter 6, each point has q^5 opposite points
    assert Dm.max() == 6 and ((Dm[:N, :N] == 6).sum(1) == q ** 5).all()
    return dict(lines_of_pt=lines_of_pt, pts_of_line=pts_of_line)


def distinct_rows(lab):
    s = np.sort(lab, axis=1)
    return 1 + (s[:, 1:] != s[:, :-1]).sum(1)


def stats_static(N, q, geo, Dm, Tg, HL, Wg, grp):
    out = {}
    M = grp.M
    lp, pl = geo['lines_of_pt'], geo['pts_of_line']
    # (a) regularity of hop labels
    for k, T in enumerate(Tg[:2]):
        inv = np.empty(N, np.int64); inv[HL[k]] = np.arange(N)   # point hopping to line l
        a_line = T[inv]                                         # label of hop dart point->line
        dl = distinct_rows(a_line[lp])                          # lines through each point
        dp = distinct_rows(T[pl])                               # points on each line
        out[f'a{k+1}_lines_thru_pt_distinct_mean'] = dl.mean()
        out[f'a{k+1}_frac_pts_all_lines_distinct'] = (dl == q + 1).mean()
        out[f'a{k+1}_pts_on_line_distinct_mean'] = dp.mean()
        out[f'a{k+1}_frac_lines_all_pts_distinct'] = (dp == q + 1).mean()
    # (b) label arithmetic at a point / along lines
    T1 = Tg[0]; T2 = Tg[1] if len(Tg) > 1 else None
    def hist_stats(vals, prefix):
        h = np.bincount(vals.ravel(), minlength=M).astype(np.float64)
        out[prefix + '_support'] = float((h > 0).sum())
        out[prefix + '_coll'] = float((h ** 2).sum() / h.sum() ** 2)
    if T2 is not None:
        hist_stats(grp.SUB[T1, T2], 'b_t1mt2')
        hist_stats(grp.ADD[T1, T2], 'b_t1pt2')
    x = pl
    diffs = grp.SUB[T1[x][:, :, None], T1[x][:, None, :]]
    off = ~np.eye(q + 1, dtype=bool)[None]
    hist_stats(diffs[np.broadcast_to(off, diffs.shape)], 'b_collinear_t1diff')
    # (e) hop distances in the hexagon incidence graph
    p = np.arange(N)
    e = {}
    for k, hl in enumerate(HL[:2]):
        d = Dm[p, N + hl].astype(np.float64)
        out[f'e_d(x,s{k+1}(x))_mean'] = d.mean()
        out[f'e_d(x,s{k+1}(x))_frac_far5'] = (d == 5).mean()
        out[f'e_d(x,s{k+1}(x))_frac_d1'] = (d == 1).mean()
    if len(HL) > 1:
        dl = Dm[N + HL[0], N + HL[1]].astype(np.float64)
        out['e_d(s1,s2)_mean'] = dl.mean()
        out['e_d(s1,s2)_frac_opp6'] = (dl == 6).mean()
    return out


def run_walks(NB, M, grp, darts, srcs, maxlen, keep_at):
    """walk-holonomy DP. returns (C_at_keep_at list per batch, S = sum_{k<=maxlen} C_k per batch)."""
    U, uniq, starts, W = darts
    SH = grp.SUB[np.arange(M)[None, :], W[:, None]]          # SH[d, g] = g - w_d
    D = len(U)
    Bmax = max(1, int(2e7 // (D * M)))
    res = []
    for b0 in range(0, len(srcs), Bmax):
        s = srcs[b0:b0 + Bmax]; B = len(s)
        C = np.zeros((B, NB, M), np.int32); C[np.arange(B), s, 0] = 1
        S = np.zeros((B, NB, M), np.int64); Ck = None
        for k in range(1, maxlen + 1):
            G = C[:, U[:, None], SH]
            part = np.add.reduceat(G, starts, axis=1)
            Cn = np.zeros((B, NB, M), np.int32); Cn[:, uniq, :] = part
            C = Cn; S += C
            if k == keep_at: Ck = C.copy()
        res.append((s, Ck, S))
    return res


def stats_walks(NB, N, q, grp, Dm, flagD, allD, srcs):
    M = grp.M
    acc = dict(c_dist=0.0, c_n=0, c_all=0, z_pairs=0.0, n_pairs=0, hist=np.zeros(M), f_eff=0.0, f_cov=0.0, f_n=0)
    # (c),(d): geodesics between opposite points use the hexagon (flag) darts only; length-6 walks = geodesics
    for s, C6, _ in run_walks(NB, M, grp, flagD, srcs, 6, 6):
        for b in range(len(s)):
            opp = np.flatnonzero(Dm[s[b], :N] == 6)
            c = C6[b, opp, :].astype(np.int64)
            assert (c.sum(1) == q + 1).all(), 'geodesic count != q+1'
            dist = (c > 0).sum(1)
            acc['c_dist'] += dist.sum(); acc['c_n'] += len(opp); acc['c_all'] += (dist == q + 1).sum()
            acc['z_pairs'] += (c * (c - 1) // 2).sum(); acc['n_pairs'] += len(opp) * (q * (q + 1) // 2)
            corr = np.einsum('pg,pgd->pd', c, c[:, grp.ADD])
            corr[:, 0] -= (q + 1)
            acc['hist'] += corr.sum(0)
    # (f): walks of length <= 7 in the full base (flags + hops)
    for s, _, S in run_walks(NB, M, grp, allD, srcs, 7, 7):
        for b in range(len(s)):
            Sl = S[b, N:2 * N, :]
            tot = Sl.sum(1); dis = (Sl > 0).sum(1)
            acc['f_eff'] += (dis / tot).sum(); acc['f_cov'] += (dis / M).sum(); acc['f_n'] += N
    out = {}
    out['c_opp_distinct_mean'] = acc['c_dist'] / acc['c_n']
    out['c_opp_frac_all_distinct'] = acc['c_all'] / acc['c_n']
    out['d_apartment_zero_hol_frac'] = acc['z_pairs'] / acc['n_pairs']
    h = acc['hist']; mu = h.mean()
    out['d_apartment_hol_chi2_per_df'] = float(((h - mu) ** 2 / mu).sum() / (M - 1))
    out['f_walk_efficiency_mean'] = acc['f_eff'] / acc['f_n']
    return out


def full_stats(Pf, Lf, Wf, HL, HW, N, q, grp, geo, Dm, srcs):
    Wg, Tg = gauge(N, Pf, Lf, Wf, HL, HW, grp)
    out = stats_static(N, q, geo, Dm, Tg, HL, Wg, grp)
    flagD = dart_arrays(N, Pf, Lf, Wg, [], [], grp)
    allD = dart_arrays(N, Pf, Lf, Wg, HL, Tg, grp)
    out.update(stats_walks(2 * N, N, q, grp, Dm, flagD, allD, srcs))
    return out


def dart_arrays(N, Pf, Lf, Wg, HL, Tg, grp):
    pts = np.arange(N)
    U = [Pf, N + Lf]; V = [N + Lf, Pf]; W = [Wg, grp.NEG[Wg]]
    for hl, T in zip(HL, Tg):
        U += [pts, N + hl]; V += [N + hl, pts]; W += [T, grp.NEG[T]]
    U = np.concatenate(U); V = np.concatenate(V); W = np.concatenate(W)
    o = np.argsort(V, kind='stable'); U, V, W = U[o], V[o], W[o]
    starts = np.flatnonzero(np.r_[True, V[1:] != V[:-1]])
    return U, V[starts], starts, W


def main():
    nsamp = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    configs = [
        ('q2_j2_M44', f'{ROOT}/research/theorems/d8/q2/q2_j2_M44.txt'),
        ('q2_j1_M10', f'{ROOT}/research/theorems/d8/q2/q2_j1_M10.txt'),
        ('q3_j1_M7', f'{ROOT}/research/theorems/d8/lanneal_best_q3_j1_M7_h1.txt'),
        ('q3_j2_M20_fresh', f'{HERE}/lanneal2_q3_j2_M20_h1_s7.txt'),
        ('q4_j2_M20_212unr', f'{ROOT}/research/theorems/d8/lanneal2_q4_j2_M20_h1_s7.txt'),
    ]
    results = {}
    Dcache = {}
    t0 = time.time()
    for name, path in configs:
        L = load_file(path)
        N, q, j, M1, M2 = L['N'], L['q'], L['j'], L['M1'], L['M2']
        grp = Grp(M1, M2)
        Pf, Lf, Wf, HL, HW = structure(L['rows'], N, L['F'], j, grp)
        if q not in Dcache:
            Dm = flag_distances(N, Pf, Lf)
            Dcache[q] = (Dm, geometry(N, q, Pf, Lf, Dm))
        Dm, geo = Dcache[q]
        srcs = np.arange(N) if q < 4 else np.linspace(0, N - 1, 96).astype(np.int64)
        obs = full_stats(Pf, Lf, Wf, HL, HW, N, q, grp, geo, Dm, srcs)
        rng = np.random.default_rng(seed * 1000 + len(results))
        rnd = []
        for _ in range(nsamp):
            HLr = [rng.permutation(N) for _ in range(j)]
            HWr = [rng.integers(0, grp.M, size=N) for _ in range(j)]
            Wr = rng.integers(0, grp.M, size=L['F'])
            rnd.append(full_stats(Pf, Lf, Wr, HLr, HWr, N, q, grp, geo, Dm, srcs))
        rows = []
        for key in obs:
            vals = np.array([r[key] for r in rnd], dtype=np.float64)
            mu, sd = vals.mean(), vals.std(ddof=1)
            z = (obs[key] - mu) / sd if sd > 0 else float('nan')
            rows.append((key, float(obs[key]), float(mu), float(sd), float(z)))
        results[name] = dict(q=q, j=j, M=grp.M, rows=rows)
        print(f'== {name}  q={q} j={j} M={grp.M} N={N}  ({time.time()-t0:.0f}s)')
        for key, o, mu, sd, z in sorted(rows, key=lambda r: -abs(r[4]) if r[4] == r[4] else 0):
            print(f'   {key:40s} obs {o:10.4f}  rand {mu:10.4f} +- {sd:8.4f}  z {z:+8.2f}')
        sys.stdout.flush()
    with open(os.path.join(HERE, 'results.json'), 'w') as fh:
        json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()

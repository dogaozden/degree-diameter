"""c1 (card: BUNDLE VOLTAGES FROM PROJECTIVE PARAMETERS), q prime.

Flag (p, l) of H(q) gets the projective parameter t(p, l) in {0..q} (index q = infinity):
  p is proportional to a_l + t * b_l, with a_l = coord[LP[l][0]], b_l = coord[LP[l][1]] (so t = 0 at LP[l][0],
  t = infinity at LP[l][1]).
Second parameter j(p, l) = position of l in PL[p] (the lines through p), 0..q.

Hexagon voltage:  V(p, l) = (kappa[t(p,l)] + mu[j(p,l)]) mod m.
Extra edges: two perfect matchings M_1, M_2 (points -> lines) avoiding hexagon incidences and M_1(p) != M_2(p),
with constant or random voltages.

Usage:
  python3 bundle.py measure q m kappa mu match seed npairs
  python3 bundle.py base    q m kappa mu match seed out.txt
  kappa: lin:c | quad:c:d | rand:seed | list:v0,v1,...,vq   (q+1 values, index q = infinity)
  mu:    none | pos:d (mu[j] = d*j mod m) | rand:seed (random injective, q+1 values)
  match: const:e1,e2 | rand:seed | zero
"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load

HERE = os.path.dirname(os.path.abspath(__file__))


def inv_table(q):
    return np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)


def nf_codes(V, q, inv):
    """code of the projective normal form (first nonzero coordinate = 1) of each row of V (mod q)."""
    V = V % q
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    NF = (V * inv[lead][:, None]) % q
    w = q ** np.arange(V.shape[1], dtype=np.int64)
    return (NF * w).sum(1)


_CACHE = {}


def flag_params(q):
    """N, LP, PL, t (L, q+1) in 0..q, j (L, q+1) in 0..q, with flag (LP[l][k], l) having parameters t[l,k], j[l,k]."""
    if q in _CACHE:
        return _CACHE[q]
    N, LP, PL, coord = load(q)
    inv = inv_table(q)
    X = coord.astype(np.int64) % q
    pc = nf_codes(X, q, inv)
    a = X[LP[:, 0]]
    b = X[LP[:, 1]]
    L = N
    cand = np.zeros((L, q + 1), dtype=np.int64)
    for t in range(q):
        cand[:, t] = nf_codes((a + t * b) % q, q, inv)
    cand[:, q] = nf_codes(b, q, inv)
    pcodes = pc[LP]
    eq = pcodes[:, :, None] == cand[:, None, :]
    assert (eq.sum(2) == 1).all(), 'projective parameter not unique on some flag'
    t = eq.argmax(2).astype(np.int64)
    del eq
    # position of line l among the lines through point LP[l,k]
    eq2 = PL[LP] == np.arange(L)[:, None, None]
    assert (eq2.sum(2) == 1).all()
    j = eq2.argmax(2).astype(np.int64)
    del eq2
    _CACHE[q] = (N, LP, PL, t, j)
    return _CACHE[q]


def kappa_vals(spec, q, m, rng):
    """values in Z_m for the q+1 parameters (index q = infinity)."""
    kind, *args = spec.split(':')
    t = np.arange(q + 1, dtype=np.int64)
    if kind == 'lin':
        return (int(args[0]) * t) % m
    if kind == 'quad':
        c, d = int(args[0]), int(args[1])
        return (c * t + d * t * t) % m
    if kind == 'rand':
        r = np.random.default_rng(int(args[0]))
        return r.permutation(m)[:q + 1].astype(np.int64)
    if kind == 'list':
        return np.array([int(x) for x in args[0].split(',')], dtype=np.int64) % m
    raise ValueError(spec)


def mu_vals(spec, q, m, rng):
    kind, *args = spec.split(':')
    j = np.arange(q + 1, dtype=np.int64)
    if kind == 'none':
        return np.zeros(q + 1, dtype=np.int64)
    if kind == 'pos':
        return (int(args[0]) * j) % m
    if kind == 'rand':
        r = np.random.default_rng(int(args[0]))
        return r.permutation(m)[:q + 1].astype(np.int64)
    raise ValueError(spec)


def hex_volt(q, m, kappa, mu, seed):
    N, LP, PL, t, j = flag_params(q)
    rng = np.random.default_rng(seed)
    kv = kappa_vals(kappa, q, m, rng)
    mv = mu_vals(mu, q, m, rng)
    V = (kv[t] + mv[j]) % m
    return N, LP, PL, V


def random_matching(N, forbid, rng):
    """random perfect matching points -> lines. forbid: (N, q+1) arrays (M(p) must not be one of F[p], i.e. not
    incident) or (N,) arrays (M(p) != F[p]). Conflicts are repaired by random swaps."""
    M = rng.permutation(N).astype(np.int64)

    def bad(p):
        for F in forbid:
            if F.ndim == 2:
                if (F[p] == M[p]).any():
                    return True
            elif F[p] == M[p]:
                return True
        return False

    for _ in range(100):
        badlist = [p for p in range(N) if bad(p)]
        if not badlist:
            return M
        for p in badlist:
            if not bad(p):
                continue
            for _t in range(500):
                r = int(rng.integers(N))
                M[p], M[r] = M[r], M[p]
                if not bad(p) and not bad(r):
                    break
                M[p], M[r] = M[r], M[p]
    raise RuntimeError('matching repair failed')


def build_edges(q, m, kappa, mu, match, seed):
    N, LP, PL, V = hex_volt(q, m, kappa, mu, seed)
    L = N
    ls = np.repeat(np.arange(L), q + 1)
    ps = LP.reshape(-1).astype(np.int64)
    hexE = np.stack([ps, ls, V.reshape(-1) % m], axis=1).astype(np.int64)
    rng = np.random.default_rng(seed + 7919)
    if match.startswith('const:'):
        e1, e2 = (int(x) for x in match.split(':', 1)[1].split(','))
        vols = [np.full(N, e1), np.full(N, e2)]
    elif match.startswith('rand'):
        vols = [rng.integers(0, m, N), rng.integers(0, m, N)]
    elif match == 'zero':
        vols = [np.zeros(N, dtype=np.int64), np.zeros(N, dtype=np.int64)]
    else:
        raise ValueError(match)
    M1 = random_matching(N, [PL], rng)
    M2 = random_matching(N, [PL, M1], rng)
    E = [hexE]
    for M, vol in ((M1, vols[0]), (M2, vols[1])):
        E.append(np.stack([np.arange(N), M, vol % m], axis=1).astype(np.int64))
    return N, np.concatenate(E), (LP, PL, V, M1, M2)


def write_base(fn, N, m, E):
    with open(fn, 'w') as f:
        f.write(f'{N} {N} {m}\n')
        chunk = 1000000
        for s in range(0, len(E), chunk):
            blk = E[s:s + chunk]
            f.write('\n'.join(f'{a} {b} {c}' for a, b, c in blk.tolist()))
            f.write('\n')


def bfs_from_line(L1, N, LP, PL):
    dp = np.full(N, -1, np.int32)
    dl = np.full(N, -1, np.int32)
    dl[L1] = 0
    fl = np.array([L1], dtype=np.int64)
    level = 0
    while len(fl):
        ps = np.unique(LP[fl].reshape(-1))
        ps = ps[dp[ps] < 0]
        if len(ps) == 0:
            break
        dp[ps] = level + 1
        ls = np.unique(PL[ps].reshape(-1))
        ls = ls[dl[ls] < 0]
        dl[ls] = level + 2
        fl = ls
        level += 2
    return dp, dl


def geodesics_line_line(L1, L2, N, LP, PL, dp, dl):
    """all shortest paths from line L1 to line L2 (dist 6): returns list of vertex lists (points as ('p',id), lines ('l',id))."""
    out = []

    def rec(path):
        kind, v = path[-1]
        d = dl[v] if kind == 'l' else dp[v]
        if d == 0:
            out.append(list(reversed(path)))
            return
        if kind == 'l':
            for p in LP[v]:
                if dp[p] == d - 1:
                    rec(path + [('p', int(p))])
        else:
            for l in PL[v]:
                if dl[l] == d - 1:
                    rec(path + [('l', int(l))])

    rec([('l', int(L2))])
    return out


def geodesic_shift(path, V, LP, PL):
    """shift from (L1, 0) along path L1 = v0, p1, l1, p2, l2, p3, L2 : line->point -V, point->line +V.
    Needs the flag voltage V[l, k] with k = position of p on l."""
    S = 0
    for i in range(len(path) - 1):
        (ka, va), (kb, vb) = path[i], path[i + 1]
        if ka == 'l':   # line -> point
            l, p = va, vb
            k = int(np.flatnonzero(LP[l] == p)[0])
            S -= int(V[l, k])
        else:           # point -> line
            p, l = va, vb
            k = int(np.flatnonzero(LP[l] == p)[0])
            S += int(V[l, k])
    return S


def measure_bundles(q, m, kappa, mu, seed, npairs, rng_seed=12345):
    N, LP, PL, V = hex_volt(q, m, kappa, mu, seed)
    rng = np.random.default_rng(rng_seed)
    distinct = []
    full = 0
    tot = 0
    for it in range(npairs):
        L1 = int(rng.integers(N))
        dp, dl = bfs_from_line(L1, N, LP, PL)
        far = np.flatnonzero(dl == 6)
        L2 = int(rng.choice(far))
        geos = geodesics_line_line(L1, L2, N, LP, PL, dp, dl)
        assert len(geos) == q + 1, (len(geos), q + 1)
        shifts = [geodesic_shift(g, V, LP, PL) % m for g in geos]
        nd = len(set(shifts))
        distinct.append(nd)
        full += int(nd == q + 1)
        tot += 1
    distinct = np.array(distinct)
    return dict(mean_distinct=float(distinct.mean()), frac_full=full / tot, min_distinct=int(distinct.min()),
                q_plus_1=q + 1, pairs=tot)


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'measure':
        q, m = int(sys.argv[2]), int(sys.argv[3])
        kappa, mu, match, seed, npairs = sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7]), int(sys.argv[8])
        res = measure_bundles(q, m, kappa, mu, seed, npairs)
        print(f'q {q} m {m} kappa {kappa} mu {mu} seed {seed}: ' + ' '.join(f'{k} {v}' for k, v in res.items()))
    elif cmd == 'base':
        q, m = int(sys.argv[2]), int(sys.argv[3])
        kappa, mu, match, seed, out = sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7]), sys.argv[8]
        N, E, _ = build_edges(q, m, kappa, mu, match, seed)
        write_base(out, N, m, E)
        print('wrote', out, 'N', N, 'edges', len(E))
    else:
        raise SystemExit(__doc__)

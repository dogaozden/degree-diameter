#!/usr/bin/env python3
"""phi_lab.py (card c6, squad r2_d14D8): geometric matchings phi in cyclic lifts of H(q) + 2 extra edges per point.

Base graph: H(q) flags (points p, lines l) plus two extra edges p -> phi(p) ("phi doubled").
  mode lev   : flags carry (level 0, sub h); extra edges (level +1, sub a_p) and (level +2, sub b_p).
               Lift group Z_5 x Z_k = Z_{5k}: CRT when gcd(5,k)=1, for k = 5 (m = 25) v = level + 5*sub.
  mode plain : every voltage uniform in Z_m.
phi types (bijections points -> lines):
  rnd    random bijection
  flag   phi(p) a line through p (random perfect matching of the flag graph)
  d3     phi(p) at incidence distance 3 from p (random perfect matching of the distance-3 graph)
  d5     phi(p) at incidence distance 5 (random, repaired by swaps)
  eqrnd  Sigma-equivariant random phi (orbit bijection + random shifts), Sigma from hex/sym_q{q}.npz
  eqflag Sigma-equivariant, phi(p) a line through p
  eqd3   Sigma-equivariant, phi(p) at distance 3
  coord  phi(p) = M(psi(p)), psi(x0..x6) = (x4,x5,x6,x3,x0,x1,x2) (automorphism of the quadric), M a random flag matching
Usage: python3 phi_lab.py sweep q seeds types      (writes results_q{q}.jsonl, keeps base files only when they pass)
       python3 phi_lab.py build q type seed mode m out   (one base file)
"""
import sys, os, subprocess, json, time
import numpy as np
from math import gcd

TOOLS = '/home/user/degree-diameter/research/squads/cells/d14D8_work'
sys.path.insert(0, TOOLS)
from hexlib import load, write_base, hex_edges

HERE = os.path.dirname(os.path.abspath(__file__))
PMATCH = os.path.join(HERE, 'pmatch')
RUNS = os.path.join(HERE, 'runs')

_hex = {}
def hexdata(q):
    if q not in _hex:
        _hex[q] = load(q)
    return _hex[q]

def pmatch(adj, seed):
    """Perfect matching of left rows of adj (n x d, -1 = absent) into 0..n-1. Returns match[i] = right id."""
    n, d = adj.shape
    inp = f"{n} {d}\n" + "\n".join(" ".join(map(str, r)) for r in adj.tolist()) + "\n"
    res = subprocess.run([PMATCH, str(seed)], input=inp.encode(), capture_output=True, check=True)
    return np.array(res.stdout.split(), dtype=np.int64)

def d3_lists(q):
    N, LP, PL, coord = hexdata(q)
    D3 = np.zeros((N, q * q * (q + 1)), dtype=np.int64)
    for p in range(N):
        cols = np.unique(LP[PL[p]].reshape(-1))          # points collinear with p (incl. p)
        near = np.unique(PL[cols].reshape(-1))           # lines at distance <= 3 from p
        D3[p] = np.setdiff1d(near, PL[p], assume_unique=True)
    return D3

def sym_data(q):
    z = np.load(os.path.join(TOOLS, 'hex', f'sym_q{q}.npz'))
    d = {k: z[k] for k in z.files}
    d['S'] = int(d['S'])
    S = d['S']; N = len(d['gperm'])
    nOrb = len(d['repP'])
    LT = np.zeros((S, nOrb), dtype=np.int64)
    LT[d['shL'], d['orbL']] = np.arange(N)
    d['LT'] = LT
    return d

def normalize(Z, q):
    inv = np.zeros(q, dtype=np.int64)
    for a in range(1, q): inv[a] = pow(a, q - 2, q)
    f = (Z != 0).argmax(axis=1); ld = Z[np.arange(len(Z)), f]
    return (Z * inv[ld][:, None]) % q

def make_phi(q, typ, seed):
    N, LP, PL, coord = hexdata(q)
    rng = np.random.default_rng(1000 * seed + 17)
    if typ == 'rnd':
        return rng.permutation(N)
    if typ == 'flag':
        return pmatch(PL, seed)
    if typ in ('d3', 'd5'):
        D3 = d3_lists(q)
        if typ == 'd3':
            return pmatch(D3, seed)
        phi = rng.permutation(N)
        def bad(p, l):
            return bool(np.any(PL[p] == l) or np.any(D3[p] == l))
        V = set(p for p in range(N) if bad(p, phi[p]))
        while V:
            p = list(V)[rng.integers(len(V))]
            r = int(rng.integers(N))
            if r == p: continue
            if not bad(p, phi[r]) and not bad(r, phi[p]):
                phi[p], phi[r] = phi[r], phi[p]
                V.discard(p); V.discard(r)
        return phi
    if typ == 'coord':
        M = pmatch(PL, seed)
        X = coord.astype(np.int64)
        Y = normalize(X[:, [4, 5, 6, 3, 0, 1, 2]], q)
        pw = q ** np.arange(6, -1, -1, dtype=np.int64)
        keys = X @ pw; order = np.argsort(keys); skeys = keys[order]
        k = Y @ pw; pos = np.searchsorted(skeys, k)
        assert (skeys[pos] == k).all()
        psi = order[pos]
        return M[psi]
    if typ in ('eqrnd', 'eqflag', 'eqd3'):
        sd = sym_data(q); S = sd['S']; orbP, shP, repP = sd['orbP'], sd['shP'], sd['repP']
        orbL, shL, repL, LT = sd['orbL'], sd['shL'], sd['repL'], sd['LT']
        nOrb = len(repP)
        if typ == 'eqrnd':
            pi = rng.permutation(nOrb); t = rng.integers(0, S, nOrb)
            return LT[(shP + t[orbP]) % S, pi[orbP]]
        cand = PL[repP] if typ == 'eqflag' else d3_lists(q)[repP]
        adj = orbL[cand]
        match = pmatch(adj, seed)
        tvec = np.zeros(nOrb, dtype=np.int64)
        for i in range(nOrb):
            k = int(np.flatnonzero(adj[i] == match[i])[0])
            tvec[i] = shL[cand[i, k]]
        return LT[(shP + tvec[orbP]) % S, match[orbP]]
    raise ValueError(typ)

def crt_table(m, k):
    T = np.zeros((5, k), dtype=np.int64)
    for x in range(m): T[x % 5, x % k] = x
    return T

def build_base(q, phi, mode, m, seed, out):
    N, LP, PL, coord = hexdata(q)
    rng = np.random.default_rng(7919 * seed + m)
    ar = np.arange(N)
    if mode == 'plain':
        flags = rng.integers(0, m, LP.shape)
        e1 = rng.integers(0, m, N); e2 = rng.integers(0, m, N)
        E = [hex_edges(LP, flags), np.stack([ar, phi, e1], 1), np.stack([ar, phi, e2], 1)]
    else:
        assert m % 5 == 0; k = m // 5
        if gcd(5, k) == 1:
            T = crt_table(m, k)
            enc = lambda lev, sub: T[lev, sub]
        else:
            enc = lambda lev, sub: (lev + 5 * sub) % m
        h = rng.integers(0, k, LP.shape); a = rng.integers(0, k, N); b = rng.integers(0, k, N)
        E = [hex_edges(LP, enc(0, h)), np.stack([ar, phi, enc(1, a)], 1), np.stack([ar, phi, enc(2, b)], 1)]
    write_base(out, N, m, np.concatenate(E))
    return out

def run_check(base, q, m, sample_only=False):
    if q == 5 and m <= 64:
        cmd = [os.path.join(TOOLS, 'lifteval'), base, '8', 'r:600:7' if sample_only else 'all']
    else:
        cmd = [os.path.join(TOOLS, 'liftevalw'), base, '8', 'r:200:7']
    res = subprocess.run(['nice', '-n', '10', 'timeout', '900'] + cmd, capture_output=True, text=True)
    line = [l for l in res.stdout.splitlines() if l.startswith('COST')]
    return int(line[0].split()[1]) if line else None

def sweep(q, seeds, types, ms_lev, ms_plain):
    N = hexdata(q)[0]
    outf = os.path.join(HERE, f'results_q{q}.jsonl')
    for typ in types:
        for seed in seeds:
            t0 = time.time()
            phi = make_phi(q, typ, seed)
            assert len(np.unique(phi)) == N, 'phi not a bijection'
            dist_ok = None
            tphi = time.time() - t0
            for mode, ms in (('lev', ms_lev), ('plain', ms_plain)):
                for m in ms:
                    base = os.path.join(RUNS, f'q{q}_{typ}_{mode}_m{m}_s{seed}.txt')
                    build_base(q, phi, mode, m, seed, base)
                    if q == 5 and m <= 64:
                        c_s = run_check(base, q, m, sample_only=True)
                        c_e = run_check(base, q, m) if c_s == 0 else None
                        rec = dict(q=q, phi=typ, seed=seed, mode=mode, m=m, cost_sample=c_s, cost_exact=c_e)
                        ok = (c_e == 0)
                    else:
                        c = run_check(base, q, m)
                        rec = dict(q=q, phi=typ, seed=seed, mode=mode, m=m, cost_r200=c)
                        ok = (c == 0)
                    if not ok:
                        os.remove(base)
                    with open(outf, 'a') as f:
                        f.write(json.dumps(rec) + '\n')
                    print(json.dumps(rec), flush=True)
            print(f'# {typ} seed {seed}: phi {tphi:.1f}s total {time.time() - t0:.1f}s', file=sys.stderr, flush=True)

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'sweep':
        q = int(sys.argv[2]); seeds = [int(x) for x in sys.argv[3].split(',')]; types = sys.argv[4].split(',')
        ms_lev = [] if sys.argv[5] == '-' else [int(x) for x in sys.argv[5].split(',')]; ms_plain = [] if sys.argv[6] == '-' else [int(x) for x in sys.argv[6].split(',')]
        sweep(q, seeds, types, ms_lev, ms_plain)
    elif cmd == 'build':
        q, typ, seed, mode, m = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5], int(sys.argv[6])
        out = sys.argv[7]
        phi = make_phi(q, typ, seed)
        build_base(q, phi, mode, m, seed, out)
        print(out)
    else:
        raise SystemExit(__doc__)

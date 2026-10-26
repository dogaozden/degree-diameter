"""c15 Wildcard B: measure walk-voltage coverage of a Z_m lift and search a parametric voltage rule.

Base: I(H(q)) (points 0..N-1, lines N..2N-1) plus two point->line matchings s1, s2 (repaired so that
no matching edge is a flag and s1(p) != s2(p)).  Voltages in Z_m:
  flag (p,l):      f(p,l) = sum_i A_i c_i(p) + B_i s_i(l) + C_i c_i(p) s_i(l)     (mod m)
  matching t, p:   a_t + sum_i D^t_i c_i(p)                                       (mod m)
where c_i(p) in {0..q-1} are the point coordinates and s_i(l) = sum over points x on l of c_i(x) mod q.

Measurement: for a source (v, 0), B_j[y] = set (bitmask over Z_m) of voltages g such that a walk of length j from
(v,0) reaches (y,g).  Cover(y) = OR_{j<=8} B_j[y]; the lift is diameter <= 8 iff Cover(y) is full for every
source v and every y (exact check = glift). Deficiency = sum_{sources, y} (m - popcount Cover(y)).

Usage: python3 wild.py search q m seed iters nsrc OUTPREFIX     (simulated annealing over the rule)
       python3 wild.py glift q m PARAMS_JSON OUTFILE            (write the glift file for a rule)
       python3 wild.py pairs q m PARAMS_JSON                    (distinct voltages by walk length, sampled pairs)
"""
import sys, json
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

FULLMASK = None


def build_base(q, seed):
    N, LP, PL, coord = load(q)
    rng = np.random.default_rng(seed)
    inc = [set(PL[p]) for p in range(N)]

    def repair(sig, other=None):
        while True:
            bad = [p for p in range(N) if sig[p] in inc[p] or (other is not None and sig[p] == other[p])]
            if not bad:
                return sig
            for p in bad:
                r = int(rng.integers(N))
                sig[p], sig[r] = sig[r], sig[p]

    s1 = repair(rng.permutation(N).astype(np.int64))
    s2 = repair(rng.permutation(N).astype(np.int64), s1)
    # flags
    L = LP.shape[0]
    fp = LP.reshape(-1).astype(np.int64)
    fl = (np.repeat(np.arange(L), q + 1) + N).astype(np.int64)
    coord = coord.astype(np.int64)
    # line coordinate sums (mod q)
    lsum = np.zeros((L, 7), dtype=np.int64)
    for l in range(L):
        lsum[l] = coord[LP[l]].sum(axis=0) % q
    return dict(N=N, q=q, coord=coord, lsum=lsum, fp=fp, fl=fl, s1=s1, s2=s2, LP=LP, PL=PL)


def edges_from_rule(base, par, m):
    """par: dict with A,B,C (7 each), D1,D2 (7 each), a1,a2. Returns undirected edge arrays (u,v,volt)."""
    N, q = base['N'], base['q']
    c = base['coord']
    ls = base['lsum']
    fp, fl = base['fp'], base['fl']
    A, B, C = (np.array(par[k], dtype=np.int64) for k in 'ABC')
    cp = c[fp]                       # (F,7)
    sl = ls[fl - N]                  # (F,7)
    fv = (cp @ A + sl @ B + (cp * sl) @ C) % m
    pts = np.arange(N)
    v1 = (par['a1'] + c @ np.array(par['D1'], dtype=np.int64)) % m
    v2 = (par['a2'] + c @ np.array(par['D2'], dtype=np.int64)) % m
    U = np.concatenate([fp, pts, pts])
    V = np.concatenate([fl, base['s1'] + N, base['s2'] + N])
    W = np.concatenate([fv, v1, v2]) % m
    return U, V, W


class Lift:
    def __init__(self, base, m):
        self.base, self.m = base, m
        self.V = 2 * base['N']
        self.full = np.uint64((1 << m) - 1)

    def set_rule(self, par):
        U, V, W = edges_from_rule(self.base, par, self.m)
        # directed arcs u->v with +w, v->u with -w
        Ua = np.concatenate([U, V]); Va = np.concatenate([V, U])
        Wa = np.concatenate([W, (-W) % self.m])
        order = np.argsort(Va, kind='stable')
        self.U = Ua[order]; self.Vt = Va[order]; self.A = Wa[order].astype(np.uint64)
        self.starts = np.searchsorted(self.Vt, np.arange(self.V))
        self.mA = (np.uint64(self.m) - self.A)

    def step(self, B):
        X = B[:, self.U]
        R = ((X << self.A) | (X >> self.mA)) & self.full
        return np.bitwise_or.reduceat(R, self.starts, axis=1)

    def cover(self, srcs, keep_levels=False):
        S = len(srcs)
        B = np.zeros((S, self.V), dtype=np.uint64)
        B[np.arange(S), srcs] = np.uint64(1)
        C = B.copy()
        levels = [B] if keep_levels else None
        for j in range(1, 9):
            B = self.step(B)
            C |= B
            if keep_levels:
                levels.append(B)
        return (C, levels) if keep_levels else C

    def deficiency(self, srcs):
        C = self.cover(srcs)
        pc = np.bitwise_count(C).astype(np.int64)
        return int((self.m - pc).sum())


def random_rule(rng, m, q):
    r = lambda: [int(x) for x in rng.integers(0, m, 7)]
    return dict(A=r(), B=r(), C=r(), D1=r(), D2=r(), a1=int(rng.integers(m)), a2=int(rng.integers(m)))


def mutate(par, rng, m):
    p = json.loads(json.dumps(par))
    keys = ['A', 'B', 'C', 'D1', 'D2']
    if rng.random() < 0.1:
        k = 'a1' if rng.random() < 0.5 else 'a2'
        p[k] = int(rng.integers(m))
    else:
        k = keys[int(rng.integers(len(keys)))]
        i = int(rng.integers(7))
        p[k][i] = int(rng.integers(m)) if rng.random() < 0.5 else (p[k][i] + int(rng.choice([-1, 1]))) % m
    return p


def search(q, m, seed, iters, nsrc, prefix):
    base = build_base(q, seed)
    rng = np.random.default_rng(seed + 1000)
    lift = Lift(base, m)
    N = base['N']
    srcs = np.concatenate([rng.choice(N, nsrc // 2, replace=False), N + rng.choice(N, nsrc - nsrc // 2, replace=False)])
    best = None
    for restart in range(3):
        par = random_rule(rng, m, q)
        lift.set_rule(par)
        cur = lift.deficiency(srcs)
        T0 = max(1.0, cur * 0.05)
        for it in range(iters):
            T = T0 * (1 - it / iters) + 1e-9
            cand = mutate(par, rng, m)
            lift.set_rule(cand)
            d = lift.deficiency(srcs)
            if d <= cur or rng.random() < np.exp(-(d - cur) / T):
                par, cur = cand, d
                if best is None or cur < best[0]:
                    best = (cur, json.loads(json.dumps(par)))
            if cur == 0:
                break
        print(f'restart {restart} done, cur={cur}, best so far={best[0]}', flush=True)
        if best[0] == 0:
            break
    json.dump({'q': q, 'm': m, 'seed': seed, 'nsrc': nsrc, 'deficiency': best[0], 'rule': best[1]},
              open(prefix + '_best.json', 'w'), indent=1)
    print('best deficiency on sampled sources', best[0], best[1])


def write_glift(q, m, seed, par, outfile):
    base = build_base(q, seed)
    U, V, W = edges_from_rule(base, par, m)
    N = base['N']
    with open(outfile, 'w') as f:
        f.write(f'Z {m}\n{2 * N}\n')
        f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
        for u, v, w in zip(U, V, W):
            f.write(f'{u} {v} {w}\n')


def pairs(q, m, seed, par, npairs=6):
    base = build_base(q, seed)
    lift = Lift(base, m); lift.set_rule(par)
    N = base['N']
    rng = np.random.default_rng(7)
    srcs = np.array([int(rng.integers(N))])
    C, levels = lift.cover(srcs, keep_levels=True)
    s = srcs[0]
    ys = rng.choice(2 * N, npairs, replace=False)
    for y in ys:
        col = 'same' if (y < N) == (s < N) else 'opp'
        fam = []
        for j, Bj in enumerate(levels):
            if j == 0:
                continue
            x = int(Bj[0, y])
            if x:
                fam.append(f'len{j}:{bin(x).count("1")}')
        print(f'pair (src {s}, y {y}, {col}): cover {bin(int(C[0, y])).count("1")}/{m}  per-length distinct voltages: {" ".join(fam)}')


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'search':
        search(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7])
    elif cmd == 'glift':
        q, m = int(sys.argv[2]), int(sys.argv[3])
        par = json.load(open(sys.argv[4]))
        write_glift(q, m, par['seed'], par['rule'], sys.argv[5])
    elif cmd == 'pairs':
        q, m = int(sys.argv[2]), int(sys.argv[3])
        par = json.load(open(sys.argv[4]))
        pairs(q, m, par['seed'], par['rule'])

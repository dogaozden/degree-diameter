"""c2: two independent pencil axes + free block layouts B1 = f1(PG(1,9)), B2 = f2(PG(1,9)) in Z_m.
Base = I(H(9)) + two parallel matchings p -- delta(p) (delta = research/squads/r1_d8c/c5/dual9.phi, 'same' mode),
hexagon voltages 0. beta_1(p) = f1[c1(p)] (axis 1 = a1^perp cap a1'^perp), beta_2(p) = f2[c2(p)] (axis 2).
Points on an axis get a random index (seeded).
Usage:
  layout.py eval M F1 F2 AXSEED SEEDS        F1,F2 = 10 comma-separated ints in Z_M; SEEDS e.g. 1,2,3
  layout.py search M ITERS AXSEED RNGSEED [F1 F2]   hill climb on glift cost (r:64:1); writes best_M_AX_RNG.json
"""
import sys, os, subprocess, json, time
import numpy as np
D = '/home/user/degree-diameter/research/squads/cells/d10D8_work'
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D)
from hexlib import load

GLIFT = os.path.join(D, 'glift')
q = 9
N, LP, PL, coord = load(q)
phi = np.fromfile('/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi', dtype=np.int32).astype(np.int64)
assert phi.shape[0] == 2 * N
C = coord.astype(np.int64)


def gf_tables(q):
    """copy of pencil_dual.gf_tables (GF(9) in hexgen2.c encoding, x^2+1)."""
    polys = {4: ([1, 1], 2), 8: ([1, 1, 0], 3), 9: ([1, 0], 2), 16: ([1, 1, 0, 0], 4), 25: ([2, 0], 2),
             27: ([1, 2, 0], 3), 32: ([1, 0, 1, 0, 0], 5)}
    p = next(d for d in range(2, q + 1) if q % d == 0)
    cfs, e = polys.get(q, ([0], 1))
    def dig(x):
        out = []
        for _ in range(e):
            out.append(x % p); x //= p
        return out
    def enc(v):
        s, pw = 0, 1
        for d in v:
            s += d * pw; pw *= p
        return s
    ADD = [[enc([(u + v) % p for u, v in zip(dig(x), dig(y))]) for y in range(q)] for x in range(q)]
    MUL = [[0] * q for _ in range(q)]
    for x in range(q):
        for y in range(q):
            a, b = dig(x), dig(y)
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if not f:
                    continue
                r[k] = 0
                for i in range(e):
                    r[k - e + i] = (r[k - e + i] - f * cfs[i]) % p
            MUL[x][y] = enc(r[:e])
    NEG = [next(y for y in range(q) if ADD[x][y] == 0) for x in range(q)]
    INV = [0] + [next(y for y in range(q) if MUL[x][y] == 1) for x in range(1, q)]
    return ADD, MUL, NEG, INV

ADD, MUL, NEG, INV = gf_tables(q)
PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
TWO = ADD[1][1]


def bform(x, y):
    acc = 0
    for i, j in PAIRS:
        acc = ADD[acc][MUL[x[i]][y[j]]]
    return ADD[acc][NEG[MUL[TWO][MUL[x[3]][y[3]]]]]


def pencil(axseed, salt):
    """index in 0..q of c(p) = [b(a,p):b(a',p)] for a random axis pair; index q = infinity; axis points random."""
    rng = np.random.default_rng(axseed * 1000 + salt)
    a, a2 = rng.integers(0, q, 7), rng.integers(0, q, 7)
    c = np.empty(N, dtype=np.int64)
    for p in range(N):
        s_, t_ = bform(C[p], a), bform(C[p], a2)
        if t_ != 0:
            c[p] = MUL[s_][INV[t_]]
        elif s_ != 0:
            c[p] = q
        else:
            c[p] = -1
    spec = rng.integers(0, q + 1, N)
    return np.where(c < 0, spec, c)

_cache = {}
def coords(axseed):
    if axseed not in _cache:
        _cache[axseed] = (pencil(axseed, 1), pencil(axseed, 2))
    return _cache[axseed]

# static part: hexagon edges (voltage 0), built once
_hex = None
def hex_block():
    global _hex
    if _hex is None:
        lines = []
        for l in range(N):
            for p in LP[l]:
                lines.append(f'{p} {N + l} 0')
        _hex = '\n'.join(lines) + '\n'
    return _hex


def write_file(path, m, f1, f2, axseed):
    c1, c2 = coords(axseed)
    v1 = (np.asarray(f1, dtype=np.int64)[c1]) % m
    v2 = (np.asarray(f2, dtype=np.int64)[c2]) % m
    pp = np.arange(N)
    out = [f'Z {m}', str(2 * N), ' '.join(['0'] * N + ['1'] * N), hex_block().rstrip('\n')]
    match = [f'{p} {phi[p]} {v1[p]}\n{p} {phi[p]} {v2[p]}' for p in range(N)]
    with open(path, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
        fh.write('\n'.join(match) + '\n')


def glift_cost(path, seed):
    cmd = ['timeout', '900', 'nice', '-n', '10', GLIFT, path, f'r:64:{seed}']
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    tok = r.stdout.split()
    if not tok or tok[0] != 'COST':
        raise RuntimeError(r.stdout + r.stderr)
    return int(tok[1]), r.stdout.strip()


def evaluate(m, f1, f2, axseed, seeds, tag='tmp'):
    path = os.path.join(HERE, f'_{tag}_{m}_{axseed}.txt')
    write_file(path, m, f1, f2, axseed)
    res = []
    for s in seeds:
        cost, line = glift_cost(path, s)
        res.append(cost)
        if cost != 0:
            break
    os.remove(path)
    return res


def default_layout(m):
    f1 = [1 + j for j in range(q + 1)]
    f2 = [q + 2 + j for j in range(q + 1)]
    return f1, f2


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'eval':
        m = int(sys.argv[2]); f1 = [int(x) for x in sys.argv[3].split(',')]
        f2 = [int(x) for x in sys.argv[4].split(',')]; ax = int(sys.argv[5])
        seeds = [int(x) for x in sys.argv[6].split(',')]
        t = time.time()
        print(evaluate(m, f1, f2, ax, seeds, tag='ev'), 'time', round(time.time() - t, 2))
    if mode == 'search':
        import random, math
        m = int(sys.argv[2]); iters = int(sys.argv[3]); ax = int(sys.argv[4]); rs = int(sys.argv[5])
        rnd = random.Random(rs)
        if len(sys.argv) > 7:
            f1 = [int(x) for x in sys.argv[6].split(',')]; f2 = [int(x) for x in sys.argv[7].split(',')]
        elif rs % 2 == 0:
            f1, f2 = default_layout(m)
        else:
            vals = list(range(m)); rnd.shuffle(vals)
            f1, f2 = vals[:q + 1], vals[q + 1:2 * (q + 1)]
        f1 = [x % m for x in f1]; f2 = [x % m for x in f2]
        cur = evaluate(m, f1, f2, ax, [1], tag=f's{rs}')[0]
        best = (cur, list(f1), list(f2))
        t0 = time.time()
        for it in range(iters):
            nf1, nf2 = list(f1), list(f2)
            blk = nf1 if rnd.random() < 0.5 else nf2
            j = rnd.randrange(q + 1)
            used = set(blk)
            cand = [v for v in range(m) if v not in used]
            if not cand:
                continue
            blk[j] = rnd.choice(cand)
            new = evaluate(m, nf1, nf2, ax, [1], tag=f's{rs}')[0]
            # accept ties and improvements; occasionally accept a worse move (log-scale annealing)
            T = 0.25 * (1 - it / iters) + 0.02
            if new <= cur or rnd.random() < math.exp(-(math.log(new + 1) - math.log(cur + 1)) / T):
                f1, f2, cur = nf1, nf2, new
                if cur < best[0]:
                    best = (cur, list(f1), list(f2))
            print(f'm{m} it{it} cur {cur} best {best[0]} t={time.time()-t0:.0f}s', flush=True)
            if best[0] == 0:
                break
        bc, bf1, bf2 = best
        val = evaluate(m, bf1, bf2, ax, [2, 3], tag=f'v{rs}') if bc == 0 else None
        out = {'m': m, 'axseed': ax, 'rng': rs, 'f1': bf1, 'f2': bf2, 'cost_seed1': bc, 'seeds23': val}
        with open(os.path.join(HERE, f'best_{m}_{ax}_{rs}.json'), 'w') as fh:
            json.dump(out, fh)
        print('BEST', json.dumps(out), flush=True)

"""Card c4 (squad d5relax-r1): large-neighbourhood search with an exact MIP.
Repeat: choose a region R of points of W(q); keep T minus R fixed; solve exactly with HiGHS the problem
"maximise |T'|, T' = (T minus R) plus a subset of R that keeps the whole set relaxed".  Accept if |T'| >= |T|.
Constraints (x_v binary for v in R, F = T minus R fixed):
  - every line: sum of x over R-points of L <= 2 - |F on L|
  - v in R, two lines L1 != L2 through v: x(L1-v) + x(L2-v) + 3 x_v <= 4 - |F on (L1-v) u (L2-v)|
  - p in F: sum of x over R-neighbours of p <= 1 - |F-neighbours of p|
Random tie-breaking in the objective gives plateau moves.
usage: python3 lns.py q START SECONDS SEED OUT [MIP_TL] [SCALE or LO,HI]     (START, OUT: rtabu format)"""
import sys, os, time, random, json
import numpy as np
import highspy

ROOT = '/home/user/degree-diameter/research/theorems/d5relax'
q = int(sys.argv[1]); start = sys.argv[2]; total = float(sys.argv[3]); seed = int(sys.argv[4]); out = sys.argv[5]
mip_tl = float(sys.argv[6]) if len(sys.argv) > 6 else 20.0
# SCALE multiplies the region sizes of the hint (8-15 lines etc.); "lo,hi" draws a scale per iteration from [lo, hi]
SCALE_RANGE = [float(v) for v in (sys.argv[7] if len(sys.argv) > 7 else '1').split(',')]
SCALE = SCALE_RANGE[0]
rng = random.Random(seed)
pre = os.path.join(ROOT, 'data', 'W%d' % q)
n = (q + 1) * (q * q + 1)
adjl = open(pre + '_adj.txt').read().strip().split('\n')
assert int(adjl[0]) == n
nbr = [set(map(int, l.split()[1:])) for l in adjl[1:]]
L = [list(map(int, s.split())) for s in open(pre + '_lines.txt').read().strip().split('\n')[1:]]
assert len(L) == n and all(len(l) == q + 1 for l in L)
sp = list(map(int, open(pre + '_spread.txt').read().split())); assert len(sp) == n
plines = [[] for _ in range(n)]
for i, l in enumerate(L):
    for p in l: plines[p].append(i)
for p in range(n):  # the line structure must reproduce the collinearity graph
    s = set()
    for i in plines[p]: s |= set(L[i]) - {p}
    assert s == nbr[p]
spread_pts = [[] for _ in range(q * q + 1)]
for p in range(n): spread_pts[sp[p]].append(p)
INF = highspy.kHighsInf

def read_set(path):
    s = open(path).read().strip()
    if s.startswith('[') or s.startswith('{'):
        T = json.loads(s); T = T['T'] if isinstance(T, dict) else T
    else:
        T = [int(x) for x in s.split()[1:]]
    return sorted(set(int(x) for x in T))

def relaxed(T):
    S = set(T)
    return len(T) > 0 and all(len(nbr[p] & S) <= 1 for p in T)

def write_set(T, path):
    with open(path + '.tmp', 'w') as f:
        f.write('%d\n' % len(T)); f.write('\n'.join(map(str, sorted(T))) + '\n')
    os.replace(path + '.tmp', path)

def region(kind, T):
    global SCALE
    SCALE = rng.uniform(SCALE_RANGE[0], SCALE_RANGE[-1]) if len(SCALE_RANGE) > 1 else SCALE_RANGE[0]
    if kind == 'lines':
        R = set()
        for li in rng.sample(range(n), min(n, rng.randint(round(8 * SCALE), round(15 * SCALE)))): R |= set(L[li])
    elif kind == 'tlines':  # lines meeting T
        cand = sorted({li for p in T for li in plines[p]})
        R = set()
        for li in rng.sample(cand, min(len(cand), rng.randint(round(8 * SCALE), round(15 * SCALE)))): R |= set(L[li])
    elif kind == 'nbh':
        R = set()
        for _ in range(max(1, round(rng.choice([2, 3]) * SCALE))):
            p = rng.choice(T) if (T and rng.random() < 0.5) else rng.randrange(n)
            R |= nbr[p] | {p}
    elif kind == 'spread':
        R = set()
        for s in rng.sample(range(q * q + 1), min(q * q + 1, rng.randint(round(10 * SCALE), round(20 * SCALE)))): R |= set(spread_pts[s])
    return R

def solve(T, R, tl):
    Tset = set(T)
    Rl = sorted(R); ridx = {p: i for i, p in enumerate(Rl)}; m = len(Rl)
    F = Tset - R
    lineF = [sum(1 for p in l if p in F) for l in L]
    lo, up, starts, idx, val = [], [], [], [], []
    def addrow(lb, ub, ids, vals):
        starts.append(len(idx)); idx.extend(ids); val.extend(vals); lo.append(lb); up.append(ub)
    for li, l in enumerate(L):
        Rs = [ridx[p] for p in l if p in ridx]
        if Rs and len(Rs) + lineF[li] > 2:
            addrow(-INF, 2 - lineF[li], Rs, [1.0] * len(Rs))
    for v in Rl:
        vi = ridx[v]
        per = []
        for li in plines[v]:
            per.append(([ridx[p] for p in L[li] if p != v and p in ridx], lineF[li]))
        for a in range(len(per)):
            Ra, ca = per[a]
            for b in range(a + 1, len(per)):
                Rb, cb = per[b]
                c = ca + cb
                if len(Ra) + len(Rb) + 3 <= 4 - c: continue
                addrow(-INF, 4 - c, Ra + Rb + [vi], [1.0] * (len(Ra) + len(Rb)) + [3.0])
    for p in F:
        Rs = [ridx[u] for u in nbr[p] if u in ridx]
        dF = len(nbr[p] & F)
        if len(Rs) > 1 - dF:
            addrow(-INF, 1 - dF, Rs, [1.0] * len(Rs))
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('threads', 1)
    h.setOptionValue('time_limit', float(tl))
    h.setOptionValue('mip_abs_gap', 0.5)   # objective = cardinality + eps with eps total < 0.4: exact cardinality
    h.setOptionValue('mip_rel_gap', 0.0)
    h.setOptionValue('random_seed', rng.randrange(1 << 30))
    h.addVars(m, np.zeros(m), np.ones(m))
    cols = np.arange(m, dtype=np.int32)
    h.changeColsIntegrality(m, cols, np.array([1] * m, dtype=np.uint8))  # 1 = integer
    eps = np.array([rng.random() * 0.4 / max(1, m) for _ in range(m)])
    h.changeColsCost(m, cols, -(1.0 + eps))
    if lo:
        h.addRows(len(lo), np.array(lo, dtype=float), np.array(up, dtype=float), len(idx),
                  np.array(starts, dtype=np.int32), np.array(idx, dtype=np.int32), np.array(val, dtype=float))
    x0 = [1.0 if Rl[i] in Tset else 0.0 for i in range(m)]
    sol = highspy.HighsSolution(); sol.col_value = x0; sol.value_valid = True
    h.setSolution(sol)
    t0 = time.time(); h.run(); dt = time.time() - t0
    st = h.modelStatusToString(h.getModelStatus())
    s2 = h.getSolution()
    if not s2.value_valid:
        return None, st, dt, len(lo)
    x = s2.col_value
    newT = sorted(F | {Rl[i] for i in range(m) if x[i] > 0.5})
    return newT, st, dt, len(lo)

def main():
    T = read_set(start)
    assert relaxed(T), 'start set is not relaxed'
    best = list(T)
    write_set(best, out)
    t0 = time.time(); it = 0
    kinds = ['lines', 'tlines', 'nbh', 'spread']
    stats = {k: [0, 0] for k in kinds}   # [tries, accepted improvements]
    print('start %d' % len(T), flush=True)
    while True:
        el = time.time() - t0
        if el > total - 2: break
        tl = min(mip_tl, total - el)
        kind = rng.choice(kinds)
        R = region(kind, T)
        if not R: continue
        it += 1
        tr = len(R & set(T))
        newT, st, dt, nrow = solve(T, R, tl)
        if newT is None:
            print('it %d %s |R|=%d no solution (%s)' % (it, kind, len(R), st), flush=True); continue
        ok = relaxed(newT)
        stats[kind][0] += 1
        if not ok:
            print('it %d %s: MIP solution NOT relaxed, rejected' % (it, kind), flush=True); continue
        diff = len(set(newT) ^ set(T))
        if len(newT) >= len(T):
            if len(newT) > len(T): stats[kind][1] += 1
            if diff: stats[kind].append(0)
            T = newT
        if len(T) > len(best):
            best = list(T); write_set(best, out)
        print('it %d %-6s |R|=%3d |T&R|=%2d rows=%5d %-12s %5.1fs  |T|=%d best=%d sym.diff=%d' % (
            it, kind, len(R), tr, nrow, st, dt, len(T), len(best), diff), flush=True)
    print('done: iterations %d, best %d, time %.0f s' % (it, len(best), time.time() - t0), flush=True)
    print('stats (tries, improvements):', stats, flush=True)
    print('final |T| %d relaxed %s' % (len(T), relaxed(T)), flush=True)

if __name__ == '__main__':
    main()

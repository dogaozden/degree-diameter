"""SA for k gadget frames in PG(2,q) (Singer labels) with every plane vertex loaded <= 2 (Delta = q+3),
then build, repair and check.  python3 kframe_sa.py q k restarts iters seed"""
import itertools, json, math, random, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences
from repair import repair

q, k, restarts, iters, seed = map(int, sys.argv[1:6])
rng = random.Random(seed)
points, lines = singer_plane(q); n = len(points); Delta = q + 3
thru = [[j for j in range(n) if p in lines[j]] for p in points]
LT = {}
for j, L in enumerate(lines):
    for a, b in itertools.combinations(sorted(L), 2): LT[a, b] = j
lt = lambda a, b: LT[min(a, b), max(a, b)]


def loadsets(fr):
    A, ell, X = fr
    P = set(lines[ell])
    for x in X: P |= lines[lt(A, x)]
    L = set(thru[A])
    for x in X: L |= set(thru[x])
    return P, L


def rand_frame():
    ell = rng.randrange(n); A = rng.choice([p for p in points if p not in lines[ell]])
    return (A, ell, tuple(rng.sample(sorted(lines[ell]), 4)))


def mutate(fr):
    A, ell, X = fr; r = rng.random()
    if r < 0.5:
        others = [p for p in lines[ell] if p not in X]; X = list(X); X[rng.randrange(4)] = rng.choice(others)
        return (A, ell, tuple(X))
    if r < 0.8:
        return (rng.choice([p for p in points if p not in lines[ell]]), ell, X)
    return rand_frame()


def total_cost(lp, ll, frames):
    c = sum(max(0, x - 2) for x in lp) + sum(max(0, x - 2) for x in ll)
    sp = [x for f in frames for x in (f[0],) + f[2]]
    c += 3 * (len(sp) - len(set(sp)))
    return c


def build(frs):
    inc = gadget_incidences(lines, frs)
    pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
    ids = {v: i for i, v in enumerate(pts + lns)}
    return len(ids), sorted((ids[a], ids[b]) for a, b in inc), [0] * len(pts) + [1] * len(lns)


for rs in range(restarts):
    frames = [rand_frame() for _ in range(k)]
    lp = [0] * n; ll = [0] * n; S = []
    for f in frames:
        P, L = loadsets(f); S.append((P, L))
        for x in P: lp[x] += 1
        for x in L: ll[x] += 1
    c = total_cost(lp, ll, frames)
    for it in range(iters):
        if c == 0: break
        T = 1.5 * (1 - it / iters) + 0.1
        g = rng.randrange(k); nf = mutate(frames[g]); P2, L2 = loadsets(nf); P1, L1 = S[g]
        for x in P1: lp[x] -= 1
        for x in L1: ll[x] -= 1
        for x in P2: lp[x] += 1
        for x in L2: ll[x] += 1
        old = frames[g]; frames[g] = nf
        c2 = total_cost(lp, ll, frames)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2; S[g] = (P2, L2)
        else:
            frames[g] = old
            for x in P2: lp[x] -= 1
            for x in L2: ll[x] -= 1
            for x in P1: lp[x] += 1
            for x in L1: ll[x] += 1
    print(f'restart {rs}: cost {c}', flush=True)
    if c: continue
    frs = []
    for A, ell, X in frames:
        P = next(p for p in sorted(lines[ell]) if p not in X); frs.append((A, ell, P, list(X)))
    N, E, side = build(frs)
    md = lib.max_degree(N, E)
    E2 = repair(N, E, side, Delta, 3, verbose=True) if md <= Delta else None
    ok = E2 is not None and lib.is_valid(N, E2, Delta, 3)
    print(f'  n={N} maxdeg={md} valid={ok}', flush=True)
    json.dump(frs, open(HERE / 'runs' / f'kframe_q{q}_k{k}_s{seed}_r{rs}.json', 'w'))
    if ok:
        out = HERE / 'graphs' / f'kframe_q{q}_k{k}_d{Delta}_n{N}.json'
        out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E2]}))
        print('  wrote', out, flush=True); break

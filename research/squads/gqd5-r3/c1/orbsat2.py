# Card r3c1: orbit-union search for relaxed sets of W(9).  Usage: orbsat2.py H1.npy [maxorbits] [seconds]
# For a list of subgroups (given by generators taken from H1), compute point orbits, keep the orbits that are
# relaxed by themselves, and solve max sum |O| x_O exactly (RC2 MaxSAT) subject to: no point p of T has two T-neighbours
# (collinear) and no two T-points lie on one S-line.  Writes the best union to best_orb.json when it improves.
import sys, json, time, random, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
G = W(9); n = G.np; col = G.col
S = regular_spread_W(G)
sline = np.full(n, -1)
for k, L in enumerate(S):
    for p in G.lines[L]: sline[p] = k
nbr = [np.array([r for L in G.plines[p] for r in G.lines[L] if r != p]) for p in range(n)]
H = np.load(sys.argv[1])
MAXO = int(sys.argv[2]) if len(sys.argv) > 2 else 400
TL = float(sys.argv[3]) if len(sys.argv) > 3 else 60

def orbits_of(gens):
    par = list(range(n))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for p in range(n):
            a, b = f(p), f(int(g[p]))
            if a != b: par[a] = b
    lab = np.array([f(p) for p in range(n)])
    cls = {}
    for p in range(n): cls.setdefault(lab[p], []).append(p)
    return list(cls.values())

def relaxed(T):
    Ts = set(T)
    for p in T:
        if sum(1 for r in nbr[p] if r in Ts) > 1: return False
        if any((sline[r] == sline[p]) for r in T if r != p): return False
    return True

def solve(orbs, tl):
    good = [O for O in orbs if relaxed(O)]
    m = len(good)
    if m == 0: return 0, []
    orb_of = np.full(n, -1)
    for i, O in enumerate(good):
        for p in O: orb_of[p] = i
    orb_of = [int(x) for x in orb_of]
    clauses = set()
    # S-line pairs
    for k in range(len(S)):
        mem = G.lines[S[k]]
        for a, b in itertools.combinations(mem, 2):
            ia, ib = orb_of[a], orb_of[b]
            if ia >= 0 and ib >= 0: clauses.add(frozenset((ia, ib)))
    # two neighbours of a point
    for p in range(n):
        ip = orb_of[p]
        if ip < 0: continue
        nb = [orb_of[r] for r in nbr[p] if orb_of[r] >= 0]
        nb = [x for x in nb]
        s = set(nb)
        for x, y in itertools.combinations(sorted(nb), 2):
            c = frozenset((ip, x, y))
            clauses.add(c)
    # unit: self-forbidden orbits (x alone) are removed earlier by relaxed(); ensure size>=2 clauses only
    wc = WCNF()
    for c in clauses:
        wc.append([-(v + 1) for v in c])
    for i, O in enumerate(good):
        wc.append([i + 1], weight=len(O))
    with RC2(wc, solver='g3', adapt=True, exhaust=True, minz=True) as rc2:
        model = rc2.compute()
    sel = [i for i in range(m) if model and model[i] > 0]
    T = sorted(p for i in sel for p in good[i])
    return len(T), T

if __name__ == '__main__':
    rng = random.Random(1)
    best = 0; bestT = []
    trials = []
    # whole group
    trials.append(('H1', list(H[:1])))  # placeholder replaced below
    # generator sets: pick several elements of H1 generating small subgroups
    orders = {}
    idx = list(range(len(H)))
    print('H1 size', len(H), flush=True)
    def order_of(g):
        cur = g.copy(); k = 1; idp = np.arange(n)
        while not np.array_equal(cur, idp):
            cur = g[cur]; k += 1
        return k
    def compose(a, b): return a[b]
    trials = []
    allgens = [H[i] for i in range(len(H))]
    tried = 0
    for trial in range(int(sys.argv[4]) if len(sys.argv) > 4 else 40):
        k = rng.choice([1, 1, 2, 2, 3])
        gens = [H[rng.randrange(len(H))] for _ in range(k)]
        trials.append(gens)
    trials.insert(0, [H[i] for i in range(0, len(H), 1)][:0] or [H[0]])
    results = []
    for gens in trials:
        orbs = orbits_of(gens)
        if len(orbs) > MAXO or len(orbs) < 2: 
            continue
        t0 = time.time()
        val, T = solve(orbs, TL)
        results.append((val, len(orbs), [len(O) for O in orbs][:5]))
        print('gens', len(gens), 'orbits', len(orbs), 'best union', val, 'time %.1f' % (time.time() - t0), flush=True)
        if val > best:
            best, bestT = val, T
            json.dump(bestT, open('/home/user/degree-diameter/research/squads/gqd5-r3/c1/best_orb.json', 'w'))
    print('BEST', best, flush=True)

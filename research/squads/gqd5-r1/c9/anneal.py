"""SA over hub attachments for fixed freed sets R0 (lines) and R2 (points). usage: anneal.py R0file R2file iters seed out"""
import sys, random, math, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from hubgraph import *
R0 = [int(x) for x in json.load(open(sys.argv[1]))]
R2 = [int(x) for x in json.load(open(sys.argv[2]))]
ITERS = int(sys.argv[3]); seed = int(sys.argv[4]); OUT = sys.argv[5]
rng = random.Random(seed)
NB = NA = 40
DMAX = 7
Bkeys = [('a', c) for c in R0] + [('s', s) for s in R2]
Akeys = [('b', c) for c in R0] + [('t', s) for s in R2]
Bas = {k: -1 for k in Bkeys}; Aas = {k: -1 for k in Akeys}
Y = set()
def lists():
    Bh = [[] for _ in range(NB)]; Ah = [[] for _ in range(NA)]
    for k, h in Bas.items():
        if h >= 0: Bh[h].append(k)
    for k, g in Aas.items():
        if g >= 0: Ah[g].append(k)
    return Bh, Ah
def degok():
    Bh, Ah = lists()
    dB = [len(x) for x in Bh]; dA = [len(x) for x in Ah]
    for (h, g) in Y: dB[h] += 1; dA[g] += 1
    return max(dB) <= DMAX and max(dA) <= DMAX
def cost():
    Bh, Ah = lists()
    # hubs with no slot and no Y edge are simply not present
    n, E, deg = build_graph(R0, R2, Bh, Ah, sorted(Y))
    return evaluate(n, E, 'sa%d' % seed)['bad']
cur = cost(); best = cur; bestState = None
T0, T1 = 6.0, 0.3
t0 = time.time()
for it in range(ITERS):
    T = T0 * (T1 / T0) ** (it / max(1, ITERS - 1))
    undo = None
    r = rng.random()
    if r < 0.8:
        isB = rng.random() < 0.5
        keys = Bkeys if isB else Akeys
        dct = Bas if isB else Aas
        k = rng.choice(keys)
        old = dct[k]
        new = rng.choice([-1] + list(range(NB if isB else NA)))
        if new == old: continue
        dct[k] = new
        if not degok(): dct[k] = old; continue
        undo = lambda: dct.__setitem__(k, old)
    else:
        pair = (rng.randrange(NB), rng.randrange(NA))
        if pair in Y:
            Y.remove(pair); undo = lambda: Y.add(pair)
        else:
            Y.add(pair)
            if not degok(): Y.remove(pair); continue
            undo = lambda: Y.discard(pair)
    new_cost = cost()
    if new_cost <= cur or rng.random() < math.exp(-(new_cost - cur) / T):
        cur = new_cost
        if cur < best:
            best = cur; bestState = (dict(Bas), dict(Aas), set(Y))
        if cur == 0: break
    else:
        undo()
    if it % 200 == 0:
        print('it', it, 'T %.2f' % T, 'cur', cur, 'best', best, 'time %.0f' % (time.time() - t0), flush=True)
print('FINAL best bad', best, 'iters', it + 1, flush=True)
if bestState:
    Bas2, Aas2, Y2 = bestState
    Bh = [[] for _ in range(NB)]; Ah = [[] for _ in range(NA)]
    for k, h in Bas2.items():
        if h >= 0: Bh[h].append(k)
    for k, g in Aas2.items():
        if g >= 0: Ah[g].append(k)
    n, E, deg = build_graph(R0, R2, Bh, Ah, sorted(Y2))
    res = apsp_check(n, E, 'best%d' % seed)
    print('apsp:', res)
    json.dump({'R0': R0, 'R2': R2, 'Bh': Bh, 'Ah': Ah, 'Y': sorted(Y2), 'bad': best, 'apsp': res}, open(OUT, 'w'))

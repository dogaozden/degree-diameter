"""search.py SEED TRIES KMAX PBIAS [SECS]: random greedy growth of freed flags (p in l = sigma(p)) keeping a perfect
matching (exact coverage model, pflag.matching); bias moves towards collinear / concurrent / 'point on freed line'
candidates (cheap hub requirements).  After every accepted flag set of size >= 5 the hub-graph requirements are
annealed (pflag.hub_anneal); prints the best k with perfect matching AND feasible hub graph, and the flags."""
import sys, random, time
sys.path.insert(0, '.')
from pflag import *
seed = int(sys.argv[1]); tries = int(sys.argv[2]); KMAX = int(sys.argv[3]); pbias = float(sys.argv[4])
secs = float(sys.argv[5]) if len(sys.argv) > 5 else 600
rng = random.Random(seed); t0 = time.time()
flags = []; usedP = set(); usedL = set()
best_feas = 0; best_flags = None; best_B = None
fails = 0; calls = 0; mtries = {}
def cand(kind):
    if kind == 'rand' or not flags:
        p = rng.randrange(N); l = rng.choice(lof[p])
        return p, l
    i = rng.randrange(len(flags)); p0, l0 = flags[i]
    if kind == 'online':     # new point on the freed line l0 (one patch edge, no common-neighbour hub edges)
        ps = [y for y in lines[l0] if y != p0 and y not in usedP]
        if not ps: return None
        p = rng.choice(ps); ls = [m for m in lof[p] if m not in usedL]
        if not ls: return None
        return p, rng.choice(ls)
    if kind == 'coll':       # new point collinear with p0
        ps = [y for y in range(N) if (Pm[p0] >> y & 1) and y != p0 and y not in usedP]
        if not ps: return None
        p = rng.choice(ps); ls = [m for m in lof[p] if m not in usedL]
        if not ls: return None
        return p, rng.choice(ls)
    if kind == 'conc':      # new line concurrent with l0
        ms = [m for m in range(N) if (Lm[l0] >> m & 1) and m != l0 and m not in usedL]
        if not ms: return None
        m = rng.choice(ms); ps = [y for y in lines[m] if y not in usedP]
        if not ps: return None
        return rng.choice(ps), m
    return None
kinds = ['online', 'coll', 'conc']
while fails < tries and len(flags) < KMAX and time.time() - t0 < secs:
    r = rng.random()
    if r < pbias: kind = rng.choice(kinds)
    else: kind = 'rand'
    c = cand(kind)
    if c is None: fails += 1; continue
    p, l = c
    if p in usedP or l in usedL: fails += 1; continue
    calls += 1
    sz, _ = matching(flags + [(p, l)])
    mtries[kind] = mtries.get(kind, 0) + 1
    if sz == N:
        flags.append((p, l)); usedP.add(p); usedL.add(l); fails = 0
        print('accepted k', len(flags), kind, (p, l), 'time %.0f' % (time.time() - t0), flush=True)
        if len(flags) >= 5:
            patch, commA, commB, coll, conc, NEED1, NEED2 = relations(flags)
            cst, B = hub_anneal(len(flags), patch, commA, commB, iters=60000, seed=seed)
            nE = sum(map(sum, B))
            print('  hub anneal k', len(flags), 'violations', cst, 'edges', nE, flush=True)
            if cst == 0 and len(flags) > best_feas:
                best_feas = len(flags); best_flags = list(flags); best_B = B
                print('BEST_FEAS k', best_feas, 'flags', flags, flush=True)
    else:
        fails += 1
print('DONE k', len(flags), 'best feasible k', best_feas, 'calls', calls, 'time %.0f' % (time.time() - t0))
print('FLAGS', ' '.join(f'{p}:{l}' for p, l in flags))
if best_flags:
    print('BESTFLAGS', ' '.join(f'{p}:{l}' for p, l in best_flags))

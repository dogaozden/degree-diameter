"""Greedy extension of the zero-mismatch K=4 family found by pool_sample.py (seed 7).
Pool: random flags opposite to all current members; each step adds the candidate with minimum mismatch.
Usage: python3 extend.py POOL SEED"""
import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/c1')
from lib import *

POOL, SEED = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time()
d = json.load(open('/home/user/degree-diameter/research/squads/d10D7-r3/c1/pool_sample_300_7.json'))
fam = [tuple(map(int, f)) for f in d['zero_quads'][0]]
cur = [FD(p, l) for p, l in fam]
print('start family', fam, 'mismatch', mismatch(cur), flush=True)
rng = np.random.default_rng(SEED)
raw = []
for _ in range(POOL):
    p = int(rng.integers(N)); l = int(H.PL[p, rng.integers(H.q + 1)])
    if all(opp(f, FD.__new__(FD)) if False else (f.dp[p] == 6 and f.dl[N + l] == 6 and f.dp[N + l] == 5 and f.dl[p] == 5) for f in cur):
        raw.append((p, l))
raw = list(dict.fromkeys(raw))
print('pool survivors opposite to all 4', len(raw), flush=True)
cand = [FD(p, l) for p, l in raw]
hist = {}
for K in range(5, 13):
    best = None
    scores = [mismatch(cur + [c]) for c in cand]
    m = min(scores)
    idx = [i for i, s in enumerate(scores) if s == m]
    i = int(rng.choice(idx))
    best = cand[i]
    cur.append(best)
    hist[K] = {'mismatch': m, 'n_cands': len(cand), 'n_min_ties': len(idx),
               'family': [[f.p, f.l] for f in cur]}
    print('K=%d best mismatch %d (cands %d, ties %d)' % (K, m, len(cand), len(idx)), flush=True)
    cand = [c for j, c in enumerate(cand) if j != i and opp(best, c) and all(opp(f, c) for f in cur[:-1])]
    if not cand:
        print('no candidates left', flush=True); break
    if time.time() - t0 > 900:
        print('time stop', flush=True); break
# independent check with hexkit for each recorded family
for K, v in hist.items():
    fl = [tuple(x) for x in v['family']]
    v['hexkit_mismatch'] = H.mismatch(fl)
    print('K=%d hexkit mismatch %d' % (K, v['hexkit_mismatch']), flush=True)
hist['4'] = {'mismatch': 0, 'family': fam}
json.dump(hist, open('/home/user/degree-diameter/research/squads/d10D7-r3/c1/extend_%d_%d.json' % (POOL, SEED), 'w'))
print('time', round(time.time() - t0, 1), flush=True)

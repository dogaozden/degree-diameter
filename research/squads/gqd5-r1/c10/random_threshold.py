import sys, json, random, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
def success(K, d, seed0, trials=10):
    for t in range(trials):
        rng = random.Random(seed0 * 1000 + t)
        if K <= d:
            return True, None  # complete bipartite K_{K,K} has max degree K <= d and works
        e = random_regular_bip(K, d, rng)
        kind = 'regular'
        if e is None:  # dense case: no exact d-regular sample found; use random maximal graph with max degree <= d
            e = random_maximal_bip(K, K, d, rng); kind = 'maximal'
        res = check(2 * K, [(a, b) for a, b in e])
        if res.get('valid') == 1:
            return True, (t, kind)
    return False, None
results = {}
for d in range(2, 13):
    lo, hi = d, d
    # exponential search for failing K
    while True:
        ok, _ = success(hi, d, d * 100003 + hi)
        if not ok:
            break
        lo = hi; hi *= 2
    # bisect: lo succeeds (or trivially), hi fails
    while hi - lo > 1:
        mid = (lo + hi) // 2
        ok, _ = success(mid, d, d * 100003 + mid)
        if ok: lo = mid
        else: hi = mid
    results[d] = lo
    print('check', d, lo, success(lo, d, d*100003+lo), flush=True)
    print("delta", d, "random max K (>=1 of 10 trials):", lo, "first failing K:", hi, flush=True)
json.dump(results, open('/home/user/degree-diameter/research/squads/gqd5-r1/c10/random_max.json', 'w'), indent=1)

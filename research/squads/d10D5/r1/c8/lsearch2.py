"""lsearch2.py K SEED ITERS OUTJSON: local search over k-flag sets, objective = matching deficiency (obst.py model).
Iteration-based annealing (T 1.0 -> 0.1).  Stops at deficiency 0 or after ITERS.  Writes the best state (flags,
deficiency, Hall violator sizes) to OUTJSON and FOUND/SIGMA lines to stdout when deficiency 0."""
import sys, random, math, json
sys.path.insert(0, '.')
from obst import Geo
K = int(sys.argv[1]); seed = int(sys.argv[2]); ITERS = int(sys.argv[3]); OUT = sys.argv[4]
rng = random.Random(seed)
geo = Geo(); N = geo.N
def rand_flag(used_p, used_l):
    while True:
        p = rng.randrange(N)
        if p in used_p: continue
        cand = [l for l in geo.lof[p] if l not in used_l]
        if cand: return p, rng.choice(cand)
flags = []; used_p = set(); used_l = set()
while len(flags) < K:
    p, l = rand_flag(used_p, used_l); flags.append((p, l)); used_p.add(p); used_l.add(l)
def ev(fl):
    s, mL, viol = geo.matching(fl, want_violator=True); return N - s, mL, viol
cur, mL, viol = ev(flags)
best = (cur, list(flags), mL, viol)
T0, T1 = 1.0, 0.1
it = 0
while cur > 0 and it < ITERS:
    it += 1
    T = T0 * (T1 / T0) ** (it / ITERS)
    i = rng.randrange(K)
    up = {q for j, (q, _) in enumerate(flags) if j != i}; ul = {m for j, (_, m) in enumerate(flags) if j != i}
    newf = rand_flag(up, ul)
    cand = flags[:i] + [newf] + flags[i + 1:]
    d, mL2, v2 = ev(cand)
    if d <= cur or rng.random() < math.exp(-(d - cur) / T):
        flags = cand; cur = d; mL = mL2; viol = v2
        if cur < best[0]:
            best = (cur, list(flags), mL, viol)
            print('it', it, 'best', cur, flush=True)
bd, bf, bm, bv = best
d = bd
info = {'k': K, 'seed': seed, 'iters': it, 'deficiency': d, 'flags': bf,
        'violator_points': len(bv[0]) if bv else 0, 'violator_lines': len(bv[1]) if bv else 0}
json.dump(info, open(OUT, 'w'))
print('END k', K, 'seed', seed, 'best deficiency', d, 'iters', it)
print('FLAGS', ' '.join(f'{p}:{l}' for p, l in bf))
if d == 0:
    print('FOUND k', K, 'FLAGS', ' '.join(f'{p}:{l}' for p, l in bf))
    print('SIGMA', ' '.join(map(str, bm)))

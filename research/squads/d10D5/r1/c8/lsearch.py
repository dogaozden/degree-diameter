"""lsearch.py K SEED SECONDS [INIT]: local search over k-flag sets (p on l), objective = matching deficiency
(N - max matching of the obst.py model).  Moves: replace one flag by a random flag on fresh point and line.
Accept downhill / equal always, uphill with probability exp(-d/T).  Prints FLAGS when deficiency 0."""
import sys, random, math, time
sys.path.insert(0, '.')
from obst import Geo
K = int(sys.argv[1]); seed = int(sys.argv[2]); secs = float(sys.argv[3])
rng = random.Random(seed)
geo = Geo(); N = geo.N
def rand_flag(used_p, used_l):
    while True:
        p = rng.randrange(N)
        if p in used_p: continue
        cand = [l for l in geo.lof[p] if l not in used_l]
        if cand: return p, rng.choice(cand)
flags = []
used_p = set(); used_l = set()
while len(flags) < K:
    p, l = rand_flag(used_p, used_l); flags.append((p, l)); used_p.add(p); used_l.add(l)
def deficiency(fl):
    s, mL, _ = geo.matching(fl); return N - s, mL
cur, mL = deficiency(flags)
best = cur; t0 = time.time(); it = 0
T0, T1 = 1.0, 0.15
print('start', cur, flush=True)
while cur > 0 and time.time() - t0 < secs:
    it += 1
    frac = (time.time() - t0) / secs
    T = T0 * (T1 / T0) ** frac
    i = rng.randrange(K)
    up = {q for j, (q, _) in enumerate(flags) if j != i}; ul = {m for j, (_, m) in enumerate(flags) if j != i}
    newf = rand_flag(up, ul)
    cand = flags[:i] + [newf] + flags[i + 1:]
    d, mL2 = deficiency(cand)
    if d <= cur or rng.random() < math.exp(-(d - cur) / T):
        flags = cand; cur = d; mL = mL2
        if cur < best:
            best = cur; print('it', it, 'best', best, 'T %.2f' % T, flush=True)
if cur == 0:
    print('FOUND k', K, 'FLAGS', ' '.join(f'{p}:{l}' for p, l in flags))
    print('SIGMA', ' '.join(map(str, mL)))
else:
    print('END best', best, 'cur', cur, 'iters', it)

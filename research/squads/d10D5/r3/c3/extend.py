"""extend.py K SEED TRIES "p:l ..." : keep the given uncrowded flags, add random uncrowded flags up to K; best matching."""
import sys, random
sys.path.insert(0, '.')
from gq import load, perp, lperp
from flagmatch import setup, hk
from uncrowd import P, Lp, lines, lof, q, N
K, seed, tries = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
fixed = [tuple(map(int, t.split(':'))) for t in sys.argv[4].split()]
rng = random.Random(seed); best = None
for t in range(tries):
    fl = list(fixed); order = list(range(N)); rng.shuffle(order)
    for p in order:
        if len(fl) == K: break
        if any(p in P[f] for f, _ in fl) or any(p == f for f, _ in fl): continue
        cand = [l for l in lof[p] if all(l not in Lp[m] for _, m in fl)]
        if not cand: continue
        fl.append((p, rng.choice(cand)))
    if len(fl) < K: continue
    size, _ = hk(setup(q, N, lines, lof, fl), N, N)
    if best is None or size > best[0]: best = (size, fl)
print('BEST', best[0], 'FLAGS', ' '.join(f'{p}:{l}' for p, l in best[1]))

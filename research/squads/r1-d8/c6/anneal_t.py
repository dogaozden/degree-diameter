"""Anneal point labels t(p) in Z_M (H-flags 0, one hop matching s fixed random) with cost = liftdiam unreached (sampled)."""
import math, random, sys, time, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import load, write_base, liftdiam
q = int(sys.argv[1]); M = int(sys.argv[2]); iters = int(sys.argv[3]); step = int(sys.argv[4]); tag = sys.argv[5]
H = load(q); N = H.N
rng = random.Random(5)
s = list(range(N)); rng.shuffle(s)
t = [rng.randrange(M) for _ in range(N)]
path = f'/home/user/degree-diameter/research/squads/r1-d8/c6/an_{tag}_q{q}_M{M}.txt'
def cost(t):
    write_base(path, H, M, t, s)
    return liftdiam(path, 8, step)[0]
cur = cost(t); best = cur; bestt = list(t)
t0 = time.time()
for it in range(iters):
    T = 30.0 * (0.3 / 30.0) ** (it / iters)
    p = rng.randrange(N); old = t[p]
    t[p] = (old + rng.randrange(1, M)) % M
    c = cost(t)
    if c <= cur or rng.random() < math.exp(-(c - cur) / T):
        cur = c
        if c < best:
            best = c; bestt = list(t)
            if best == 0: break
    else:
        t[p] = old
    if it % 100 == 0:
        print(f'it {it} cur {cur} best {best} T {T:.2f} secs {time.time()-t0:.0f}', flush=True)
    if time.time() - t0 > 600: break
with open(f'/home/user/degree-diameter/research/squads/r1-d8/c6/an_{tag}_q{q}_M{M}_best.txt', 'w') as fh:
    fh.write(' '.join(map(str, bestt)) + '\n')
print('final best', best, flush=True)

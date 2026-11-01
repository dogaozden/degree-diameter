import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers
p, k, r, d, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), 11
G = Frob(p, k, r); N = G.N; h = 5; W = d * (d - 1) ** (2 * h - 1)
rng = np.random.default_rng(int(sys.argv[5])); t0 = time.time(); hs = []
while time.time() - t0 < 70:
    S = [0] + [int(x) for x in rng.choice(np.arange(1, N), size=d - 1, replace=False)]
    if len(set(s % k for s in S)) < 3: continue
    XA, XB = covers(G, S, D)
    hs.append(int((~XA).sum()))
print('Z_%d x| Z_%d (N=%d) d=%d: samples %d, holes A median %d, min %d, size law %.1f' %
      (p, k, N, d, len(hs), np.median(hs), min(hs), N * np.exp(-W / N)))

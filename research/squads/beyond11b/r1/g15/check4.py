# Is the excess -I miss rate at h=3 explained by disconnected / subgroup-trapped S? Count misses split by connectivity.
import random, sys
from check import *
rng = random.Random(int(sys.argv[1])); h = int(sys.argv[2]); m = int(sys.argv[3]); trials = int(sys.argv[4])
miss_conn = 0; miss_disc = 0; n_disc = 0
for t in range(trials):
    S = random_S(m, rng)
    dist = bfs(S)
    disc = any(d < 0 for d in dist[0][:N])
    if disc: n_disc += 1
    if dist[0][idx[mI]] < 0 or dist[0][idx[mI]] > 2*h:
        if disc: miss_disc += 1
        else: miss_conn += 1
lam = (3*m)**(2*h)/N
print(f"h={h} m={m} trials={trials} lambda={lam:.1f}: disconnected S={n_disc}; -I misses in disconnected={miss_disc}, in connected={miss_conn} (rate {miss_conn/max(1,trials-n_disc):.3f} among connected; exp(-lambda/6h)={math.exp(-lam/(6*h)):.3f})")

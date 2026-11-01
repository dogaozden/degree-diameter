# Proposition C check: central c = s^-1 t with s,t in S  =>  c covered on both sides at every h >= 1 (BFS ground truth).
import random, sys
from check import *
rng = random.Random(int(sys.argv[1])); m = int(sys.argv[2]); trials = int(sys.argv[3])
Z = [g for g in els if g[0][1] == 0 and g[0][2] == 0 and g[0][0] == g[0][3]]   # central: (+-I, z)
Zset = {idx[z] for z in Z}
tested = 0; viol = 0; cov_counts = []
for t in range(trials):
    S = random_S(m, rng)
    Sset = [idx[s] for s in S]
    # central elements of the form s^-1 t (only central ones) and of the form s t^-1
    C = set()
    for s in S:
        for u in S:
            c = mul(inv(s), u)
            if idx[c] in Zset: C.add(idx[c])
    cov_counts.append(len(C))
    if not C: continue
    tested += 1
    dist = bfs(S)
    for ci in C:
        if dist[0][ci] < 0 or dist[0][ci] > 2 or dist[1][N+ci] < 0 or dist[1][N+ci] > 2:
            viol += 1
print(f"m={m} trials={trials} with nonempty C(S): {tested}; violations of 'dist<=2 on both sides': {viol}")
print("distribution of |C(S)| (central elements s^-1 t, s,t in S):", sorted(set(cov_counts)), "central group size", len(Zset))

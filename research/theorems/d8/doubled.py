"""Z_5 x Z_K lifts of H(q) + hops whose Z_5 part is the polygon cover, with the two hop matchings EQUAL (s_1 = s_2 = s:
each point x has two parallel hop edges to s(x), Z_5 voltages 1 and 2).  The double edge makes a 2-cycle at every
point and line with Z_5 voltage +-1 (a "digon"); two opposite digons give Z_5-class-0 walks that the geodesic alone
cannot (class0.py).  Z_K voltages random on flags (holonomy) and hops.  usage: doubled.py q K seed out.txt [indep|dual]  (dual: q = 3, s_1 = a duality on points, s_2 random)"""
import sys
import random
import gh
q, K, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
indep = len(sys.argv) > 5 and sys.argv[5] == 'indep'
rng = random.Random(seed)
H = gh.load(q)
N = H.N
inc = [set(int(k) for k in H.through[p]) for p in range(N)]
def matching(avoid=None):
    while True:
        s = list(range(N)); rng.shuffle(s)
        bad = [p for p in range(N) if s[p] in inc[p] or (avoid and s[p] == avoid[p])]
        for p in bad:  # repair by swaps
            for _ in range(1000):
                r = rng.randrange(N)
                if s[r] not in inc[p] and s[p] not in inc[r] and (not avoid or (s[r] != avoid[p] and s[p] != avoid[r])):
                    s[p], s[r] = s[r], s[p]; break
        if all(s[p] not in inc[p] and (not avoid or s[p] != avoid[p]) for p in range(N)):
            return s
if len(sys.argv) > 5 and sys.argv[5] == 'dual':
    import numpy as np
    phi = np.load('/home/user/degree-diameter/research/squads/r2-d8/d7/dual_q3_s1.npy')
    s1 = [int(phi[p]) - N for p in range(N)]
    bad = [p for p in range(N) if s1[p] in inc[p]]
    for p in bad:  # a duality sends an absolute point to a line through it: swap with a far point
        for r in range(N):
            if s1[r] not in inc[p] and s1[p] not in inc[r]:
                s1[p], s1[r] = s1[r], s1[p]; break
    s2 = matching(s1)
else:
    s1 = matching()
    s2 = matching(s1) if indep else s1
E = []
for k in range(N):
    for p in H.lines[k]:
        E.append((int(p), N + k, 0, rng.randrange(K)))
for p in range(N):
    c1 = rng.randrange(K); c2 = rng.randrange(K)
    E.append((p, N + s1[p], 1, c1)); E.append((p, N + s2[p], 2, c2))
with open(out, 'w') as fh:
    fh.write(f'{2 * N} 5 {K} {len(E)}\n')
    for e in E:
        fh.write('%d %d %d %d\n' % e)

#!/usr/bin/env python3
"""mkhub3.py IN.sol OUT.sol [SEED]: H=2 dmhub state -> H=3 state for the FLAGDEL variant (each freed point's own flag
edge deleted, 3 hubs per fibre).  Hub graph: own-flag matching (line-side hub (i,k) ~ point-side hub (i,k), k=0..2;
it reroutes the deleted flag edge: p -> z -> z' -> l), the old inter-flag edges mapped to hubs 0/1, then random
fill of the free slots (at most 4 hub edges per hub)."""
import sys, random, collections
import lns
S = lns.read_sol(sys.argv[1]); out = sys.argv[2]; rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
F = S['F']; k = len(F); H0 = S['H']; H = 3
hg = [int(x) for x in S['rows']['hubgraph']]
old = [(hg[e], hg[e + 1]) for e in range(0, len(hg), 2)]
pairs = set(); da = collections.Counter(); db = collections.Counter()
def add(a, b):
    if (a, b) in pairs or da[a] >= 4 or db[b] >= 4: return False
    pairs.add((a, b)); da[a] += 1; db[b] += 1; return True
for i in range(k):
    for t in range(H): add(H * i + t, H * i + t)
rng.shuffle(old)
for a, b in old:
    if a // H0 == b // H0: continue
    add(H * (a // H0) + a % H0, H * (b // H0) + b % H0)
for _ in range(20000):
    a = rng.randrange(H * k); b = rng.randrange(H * k)
    if a // H != b // H: add(a, b)
rows = S['rows']; rows['dmhub'] = rows['dmhub'][:]; rows['dmhub'][3] = '3'
rows['hubgraph'] = [str(x) for ab in sorted(pairs) for x in ab]
lns.write_sol(out, S, S['sig'], -1)
print('hub edges', len(pairs), 'flag pairs', len(set((a // H, b // H) for a, b in pairs)))

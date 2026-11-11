# build_hubs.py HUBFILE OUT.edges : d16D5 n33792 graph + one new vertex per line of HUBFILE (global ids of old vertices)
import sys
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
H = 16896; n0 = 2 * H
hubs = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
use = {}
for hb in hubs:
    for w in hb:
        use[w] = use.get(w, 0) + 1
assert max(use.values()) == 1, 'old vertex used by two hubs'
assert all(len(h) <= 17 for h in hubs)
with open(EDGES) as f:
    f.readline(); body = f.read()
n = n0 + len(hubs)
with open(sys.argv[2], 'w') as f:
    f.write(f"{n}\n"); f.write(body)
    for i, hb in enumerate(hubs):
        for w in hb:
            f.write(f"{n0 + i} {w}\n")
print('wrote', sys.argv[2], 'n', n, 'hubs', len(hubs))

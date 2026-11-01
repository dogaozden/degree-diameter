# build_orbits.py ORBFILE OUT.edges: G + the 22 translates N+t of every orbit base N (global ids, one orbit per line).
# Orbit base N lies on the non-hub side; hub t of orbit has neighbours {sh_t(w)} with sh_t: g -> g+t on controller coordinates.
import sys
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
orb = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
out = sys.argv[2]
H = 16896; n0 = 2 * H
def sh(w, t):
    off = 0 if w < H else H
    loc = w - off
    blk, y = divmod(loc, 256); j, h = divmod(blk, 22)
    return off + (j * 22 + (h + t) % 22) * 256 + y
hubs = []
for N in orb:
    for t in range(22):
        hubs.append(sorted(sh(w, t) for w in N))
side_of_N = 'B' if orb and orb[0][0] >= H else 'A'
use = {}
for hb in hubs:
    for w in hb: use[w] = use.get(w, 0) + 1
assert max(use.values()) == 1, 'old vertex used by two hubs'
assert all(len(h) <= 17 for h in hubs)
with open(EDGES) as f:
    f.readline(); body = f.read()
n = n0 + len(hubs)
with open(out, 'w') as f:
    f.write(f"{n}\n"); f.write(body)
    for i, hb in enumerate(hubs):
        for w in hb: f.write(f"{n0 + i} {w}\n")
print('wrote', out, 'n', n, 'hubs', len(hubs), 'N side', side_of_N)

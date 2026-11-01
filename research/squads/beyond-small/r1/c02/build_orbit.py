# Build G + 22 A-side hubs h_t (t in Z22) with N(h_t) = N + t (B-vertices shifted in the controller Z22 coordinate).
import json, sys
st = json.load(open(sys.argv[1])); N = st['bestN']; K = len(N)
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
out = sys.argv[2]
nA = 16896; n0 = 2 * nA
def sh(w, t):
    blk, y = divmod(w, 256); j, h = divmod(blk, 22)
    return (j * 22 + (h + t) % 22) * 256 + y
keys = [((w >> 8) // 22, w & 255) for w in N]
print('distinct (j,y) keys:', len(set(keys)) == K)
hubs = []
for t in range(22):
    hubs.append(sorted(nA + sh(w, t) for w in N))
# count-check B usage
used = [b for h in hubs for b in h]
assert len(used) == len(set(used)), 'B-vertex used twice'
with open(EDGES) as f:
    f.readline(); body = f.read()
n = n0 + 22
with open(out, 'w') as f:
    f.write(f"{n}\n"); f.write(body)
    for t, hb in enumerate(hubs):
        for b in hb: f.write(f"{n0 + t} {b}\n")
print('wrote', out, 'n', n, 'hub degree', K)

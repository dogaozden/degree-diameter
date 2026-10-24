"""Local search for a delta-invariant phi (values {0, M/2}) with no opposite pair having a single GQ 4-path offset.
usage: python3 phisearch.py q M seed iters out.json"""
import sys, random, json
from dcover import load, flags_and_orbits, pt_lines

q, M, seed, iters, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
n, L, d_pt, d_ln, inv_ln = load(q)
fid, orb, norb = flags_and_orbits(n, L, d_pt, d_ln)
pl = pt_lines(n, L)
onL = [set(s) for s in L]
col = [set() for _ in range(n)]
for s in L:
    for a in s:
        col[a].update(s)
# paths for each opposite pair: list of (orbit ids of the 4 flags)
pairs = []
for P in range(n):
    for Q in range(P + 1, n):
        if Q in col[P]:
            continue
        paths = []
        for l1 in pl[P]:
            R = next(r for r in L[l1] if Q in col[r])
            m2 = next(m for m in pl[R] if Q in onL[m])
            paths.append((orb[fid[(P, l1)]], orb[fid[(R, l1)]], orb[fid[(R, m2)]], orb[fid[(Q, m2)]]))
        pairs.append(paths)
# parity of a path = xor of bits of its 4 flag orbits (phi in {0,M/2}: signs irrelevant)
occ = [[] for _ in range(norb)]
for pi, paths in enumerate(pairs):
    for k, p in enumerate(paths):
        for o in p:
            occ[o].append((pi, k))
rng = random.Random(seed)
bits = [rng.randrange(2) for _ in range(norb)]
par = [[(bits[a] ^ bits[b] ^ bits[c] ^ bits[d]) for (a, b, c, d) in paths] for paths in pairs]
cnt1 = [sum(p) for p in par]
npath = q + 1
def bad(c):
    return c == 0 or c == npath
cost = sum(bad(c) for c in cnt1)
best = cost; bestbits = bits[:]
T = 1.0
for it in range(iters):
    o = rng.randrange(norb)
    # compute delta cost of flipping orbit o
    touched = {}
    for (pi, k) in occ[o]:
        touched[(pi, k)] = touched.get((pi, k), 0) ^ 1
    dc = {}
    for (pi, k), t in touched.items():
        if t:
            dc[pi] = dc.get(pi, 0) + (1 if par[pi][k] == 0 else -1)
    delta = 0
    for pi, d in dc.items():
        delta += bad(cnt1[pi] + d) - bad(cnt1[pi])
    if delta <= 0 or rng.random() < pow(2.718, -delta / T):
        bits[o] ^= 1
        for (pi, k), t in touched.items():
            if t:
                par[pi][k] ^= 1
        for pi, d in dc.items():
            cnt1[pi] += d
        cost += delta
        if cost < best:
            best = cost; bestbits = bits[:]
            if best == 0:
                break
    T = max(0.05, T * 0.9995)
print(f"q={q} orbits={norb} pairs={len(pairs)} best={best} after {it+1} iters")
json.dump({"q": q, "M": M, "orbit_bits": bestbits, "best": best}, open(out, "w"))

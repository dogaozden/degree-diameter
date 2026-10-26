"""Card c4 (round r5-d11D5): two-switch starts under ONE collineation C, plane trick of mkdc2.py.

usage: python3 mk2.py MODE seed out.in
  MODE 99: two 9-flag regulus switches (x* on all 9 lines of its regulus, x* not on l*, l* = the 9 moved points).
  MODE 9i: one 9-flag switch (h1) plus one incident switch (h2 with the common point R0 omitted, x* on 8 lines and l*).
Plane trick: C is tangent-type, i.e. the W-lines whose C-image is isotropic are exactly the 73 W-lines meeting one
W-line `axis`; then P0 = delta(axis) and every hyperbolic line of the plane pi = P0^perp (not through P0) has all its
delta-lines C-preserved.  h1 and h2 are two such lines; they share one point R0 (two lines of a plane meet).
sigma = delta o C on old points; a 9-flag switch sends its new point x* to its new line l*; an incident switch with
omitted point R9 sets sigma(C^-1 R9) = l* and sigma(x*) = delta(R9) (as mkdc2.py).  Two switches in MODE 99 both have
the line delta(R0) among their switch lines, so that line receives both new points (its two moved points are distinct).
Optional 4th argument "xc": moved points of different switches must also be pairwise non-collinear (fewer valid seeds).
Output: plusopt format (first line "n 9", n lines, then n sigma values).
"""
import sys, random
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *

MODE, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
XC = len(sys.argv) > 4 and sys.argv[4] == "xc"   # optional: moved points of all switches pairwise non-collinear
rng = random.Random(seed)
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)

# 1. tangent-type collineation C (preserved W-lines = W-lines meeting one W-line `axis`)
tries = 0
while True:
    tries += 1
    M = randmat(rng); C = pmap(M)
    pres = [li for li, l in enumerate(LINES) if is_W([C[p] for p in l[:2]])]
    if len(pres) == n0: continue
    axis = [li for li in range(n0) if all(set(LINES[li]) & set(LINES[m]) or li == m for m in pres)]
    if axis: break
a = axis[0]; P0 = d_ln[a]
plane = [p for p in range(n0) if p != P0 and Bf(PTS[p], PTS[P0]) == 0]
assert sorted(pres) == sorted(li for li in range(n0) if d_ln[li] == P0 or Bf(PTS[d_ln[li]], PTS[P0]) == 0)
Cinv = pmap(matinv(M))
print(f"C after {tries} tries: preserved {len(pres)} axis {axis}", file=sys.stderr)

def hyp_in_plane():
    while True:
        x, y = rng.sample(plane, 2)
        if Bf(PTS[x], PTS[y]):
            h = sorted(span(PTS[x], PTS[y]))
            if P0 not in h: return h

# 2. the two hyperbolic lines of the plane (they share one point R0)
h1 = hyp_in_plane()
while True:
    h2 = hyp_in_plane()
    if h2 != h1: break
R0 = (set(h1) & set(h2)).pop()
assert all(d_pt[R] in pres for R in h1 + h2)
if MODE == "99": specs = [(h1, None), (h2, None)]
elif MODE == "9i": specs = [(h1, None), (h2, R0)]
else: raise SystemExit("MODE must be 99 or 9i")

# 3. switch points: each moved point once; prefer C^-1(delta(p)) a W-line (coset-0 demand, as mkdc.py/mkdc2.py)
usedP = set()
def pick_ps(Ls):
    ps = []
    for L in Ls:
        prev = (usedP if XC else ps)
        cand = [p for p in LINES[L] if p not in usedP and all(p not in col[q] for q in prev)]
        good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
        pool = good or cand
        if not pool: return None
        ps.append(rng.choice(pool))
    usedP.update(ps)
    return ps

sw = []
for h, R9 in specs:
    Ls = [d_pt[R] for R in h if R != R9]
    ps = pick_ps(Ls)
    if ps is None: print("no moved points", file=sys.stderr); raise SystemExit(1)
    sw.append((h, Ls, ps, R9))
    print(f"switch {'9-flag' if R9 is None else 'incident'} lines {Ls} moved {ps} omitted {R9}", file=sys.stderr)

# 4. build the base
n = n0 + len(sw)
L2 = [list(l) for l in LINES]
sig = [d_pt[C[p]] for p in range(n0)]
for k, (h, Ls, ps, R9) in enumerate(sw):
    X = n0 + k
    for L, p in zip(Ls, ps):
        L2[L] = [X if q == p else q for q in L2[L]]
    if R9 is None:
        L2.append(list(ps)); sig.append(n0 + k)                 # 9-flag: x* -> l*
    else:
        L2.append(list(ps) + [X])                               # incident: x* on l*
        s9 = Cinv[R9]; sig[s9] = n0 + k; sig.append(d_pt[R9])   # sigma(C^-1 R9) = l*, sigma(x*) = delta(R9)
assert len(L2) == n and len(sig) == n and sorted(sig) == list(range(n))
cnt = [0] * n
for l in L2:
    assert len(set(l)) == 9
    for q in l: cnt[q] += 1
assert all(c == 9 for c in cnt)
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for l in L2: f.write(" ".join(map(str, l)) + "\n")
    for s in sig: f.write(f"{s}\n")
print(f"wrote {out} n={n}", file=sys.stderr)

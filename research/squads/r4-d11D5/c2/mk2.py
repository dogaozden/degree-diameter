"""Second new pair (point 586, line 586) on the n = 586 cost-0 base base586.in (copy of r3 c2 fail0_y901.in).
Switch types:  9flag : flags (p_i, L_i), i = 1..9, become (586, L_i) and (p_i, 586); points p_i pairwise non-collinear,
                       lines L_i pairwise disjoint.
               inc8  : as 9flag for i = 1..8, plus the flag (586, 586): line 586 = {p_1..p_8, 586}.
Far from the first insertion (point 585 / line 585): the lines L_i avoid the lines through point 585 and the lines
meeting line 585; the points p_i avoid line 585 and the points on lines through 585.
usage: python3 mk2.py type seed out.in   (type: 9flag | inc8)"""
import sys, random
mode, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
t = open("/home/user/degree-diameter/research/squads/r4-d11D5/c2/base586.in").read().split()
n, dg = int(t[0]), int(t[1]); vals = list(map(int, t[2:]))
L = [vals[i * dg:(i + 1) * dg] for i in range(n)]
sig = vals[n * dg:n * dg + n]
assert n == 586 and dg == 9 and sorted(sig) == list(range(n))
X1, l1 = 585, 585
col = [set() for _ in range(n)]
pl = [[] for _ in range(n)]
for li, s in enumerate(L):
    for a in s: col[a].update(s); pl[a].append(li)
forb_pts = {X1} | set(L[l1])
for li in pl[X1]: forb_pts |= set(L[li])
forb_lines = {l1} | set(pl[X1])
for p in L[l1]: forb_lines |= set(pl[p])
allowed_lines = [l for l in range(n) if l not in forb_lines]
K = 9 if mode == "9flag" else 8
for attempt in range(100000):
    cand = allowed_lines[:]; rng.shuffle(cand)
    lines = []
    for li in cand:
        if all(not (set(L[li]) & set(L[m])) for m in lines): lines.append(li)
        if len(lines) == K: break
    if len(lines) < K: continue
    pts = []; ok = True
    for li in lines:
        c = [p for p in L[li] if p not in forb_pts and all(p not in col[q] for q in pts)]
        if not c: ok = False; break
        pts.append(rng.choice(c))
    if ok: break
X = n; NL = n + 1
Lnew = [s[:] for s in L]
for p, li in zip(pts, lines):
    Lnew[li] = [X if q == p else q for q in Lnew[li]]
Lnew.append(pts[:] + ([X] if mode == "inc8" else []))
sigma = sig[:] + [n]
# checks
assert len(Lnew) == NL and all(len(set(s)) == dg for s in Lnew)
deg = [0] * NL
for s in Lnew:
    for a in s: deg[a] += 1
assert all(d == dg for d in deg), deg
assert sorted(sigma) == list(range(NL))
with open(out, "w") as f:
    f.write(f"{NL} {dg}\n")
    for s in Lnew: f.write(" ".join(map(str, s)) + "\n")
    for v in sigma: f.write(f"{v}\n")
print("lines", lines, "points", pts, "->", out)

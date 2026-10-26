"""Attach a third pair (point 587, line 587) to the solved K22 base (n=587, cost 0).
usage: python3 build.py VARIANT SEED OUT.in [TRIES]
  V1: z = 587 on 8 old lines delta(R), R in a hyperbolic line h3 (one R excluded), and on the new line k = 587.
      k = {587} + one moved point from each of those 8 lines (9 points).
  V2: z = 587 on l* = 585 (one moved point p0 of l* goes to k), on k, and on 7 old lines from h3 (two R excluded).
  sigma: start with sigma(587) = 587 (identity), then the best single swap (587, q) over all q (scan.py).
The K22 base lines are W(8) except 14 lines; sigma is the annealed one."""
import sys, os, random, subprocess
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r6-d11D5/c6")
from load import *
BASE = "/home/user/degree-diameter/research/d11D5/graphs/d11D5_n7044_k22.in"
n, Lb, sigb = read(BASE)
mod = [l for l in range(n0) if sorted(Lb[l]) != sorted(LINES[l])]
moved_old = set()
for l in mod: moved_old |= set(LINES[l]) - set(Lb[l])
dpt_inv = [0] * n0
for R in range(n0): dpt_inv[d_pt[R]] = R
H12 = set()                                    # points of the two K22 hyperbolic lines (h1, h2) incl. the shared R=2
for l in mod: H12.add(dpt_inv[l])
H12 |= {22, 50, 131}                           # excluded (unmodified) points of h1, h2
hyps = [span(PTS[a], PTS[b]) for a in range(n0) for b in range(a + 1, n0) if Bf(PTS[a], PTS[b])]
hyps = list({h for h in hyps})
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
def score(path):
    out = subprocess.run(["/tmp/po7", path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])
def build(variant, seed, out):
    rng = random.Random(seed)
    Z, K = n0 + 2, n0 + 2                       # new point 587 and new line 587 (n0 + 2 = 587 = n - 1 for the base of 587 points)
    Z = n; K = n                                 # n = 587 at the base, so new point id 587 and new line id 587
    while True:
        h3 = rng.choice(hyps)
        if not (set(h3) & H12): break
    h3 = sorted(h3)
    nexc = 1 if variant == "V1" else 2
    excl = rng.sample(h3, nexc)
    flagged = [R for R in h3 if R not in excl]
    L2 = [list(l) for l in Lb]
    usedP = set(moved_old)
    group = []; moves = []
    order = flagged[:]; rng.shuffle(order)
    for R in order:
        Li = d_pt[R]
        other = set()
        for R2 in flagged:
            if R2 != R: other |= set(LINES[d_pt[R2]])
        cand = [p for p in LINES[Li] if p not in usedP and all(p not in col[q] for q in group)]
        pref = [p for p in cand if p not in other] or cand
        if not pref: return None
        p = rng.choice(pref)
        group.append(p); usedP.add(p); moves.append((Li, p))
    if variant == "V2":
        cand = [p for p in sorted(moved_old) if p in Lb[585] and p not in (585, 586) and all(p not in col[q] for q in group)]
        if not cand: return None
        p0 = rng.choice(cand)
        L2[585] = [Z if q == p0 else q for q in L2[585]]
        group.append(p0)
    for Li, p in moves:
        L2[Li] = [Z if q == p else q for q in L2[Li]]
    kline = [Z] + group
    L2.append(sorted(kline))
    sig = list(sigb) + [K]                       # sigma(Z) = K initially (identity)
    if V2_ok(L2) is False: return None
    write(out, n + 1, L2, sig)
    return h3, excl
def V2_ok(L2):
    deg = [0] * (n + 1)
    for l in L2:
        if len(set(l)) != 9: return False
        for p in l: deg[p] += 1
    return all(d == 9 for d in deg)
def best_swap(src, dst):
    nn, L, sig = read(src)
    best = None
    tmp = dst + ".scan"
    for q in range(nn - 1):
        s2 = list(sig); s2[nn - 1], s2[q] = s2[q], s2[nn - 1]
        write(tmp, nn, L, s2)
        c = score(tmp)
        if best is None or c < best[0]: best = (c, q)
    s2 = list(sig); q = best[1]; s2[nn - 1], s2[q] = s2[q], s2[nn - 1]
    write(dst, nn, L, s2)
    os.remove(tmp)
    return best
if __name__ == "__main__":
    variant, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    tries = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    results = []
    for t in range(tries):
        tmp = f"{out}.t{t}"
        r = build(variant, seed * 1000 + t, tmp)
        if r is None: print("try", t, "build failed"); continue
        c0 = score(tmp)
        bc, q = best_swap(tmp, tmp + ".sw")
        print(f"try {t} h3 {r[0][0]}..{r[0][-1]} excl {r[1]} start(identity) {c0} best-swap {bc} (partner q={q})", flush=True)
        results.append((bc, t))
    if results:
        bc, t = min(results)
        os.replace(f"{out}.t{t}.sw", out)
        for tt in range(tries):
            for f in (f"{out}.t{tt}", f"{out}.t{tt}.sw"):
                if os.path.exists(f): os.remove(f)
        print("best", bc, out)

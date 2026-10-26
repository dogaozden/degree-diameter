"""c8: 9-flag switch base (W(8) + x* + l*) WITHOUT the jump pair sigma(x*) = l*.
Switch as in research/d11D5/plus/mkplus.py (spread/random), sigma = delta on old points.
Then sigma(x*) <- delta(q) and sigma(q) <- l*  for a chosen old point q (a sigma swap of x* and q).
usage: python3 mkswitch.py mode seed q out.in      (q = -1: keep sigma(x*)=l*; q = 'scan' not allowed here)
Writes the po7 .in format: 'n dg', n lines of point ids, n sigma values."""
import sys, random, os
os.chdir("/home/user/degree-diameter/research/d11D5")
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
from dcover import load

def switch(mode, seed):
    rng = random.Random(seed)
    n, L, d_pt, d_ln, inv = load(8)
    L = [list(s) for s in L]
    col = [set() for _ in range(n)]
    for s in L:
        for a in s: col[a].update(s)
    def concurrent(a, b): return bool(set(L[a]) & set(L[b]))
    for attempt in range(100000):
        if mode == "spread":
            lines = []
            cand = list(range(n)); rng.shuffle(cand)
            for li in cand:
                if all(not concurrent(li, m) for m in lines): lines.append(li)
                if len(lines) == 9: break
        else:
            lines = rng.sample(range(n), 9)
        pts = []; ok = True
        for li in lines:
            c = [p for p in L[li] if all(p not in col[q] for q in pts)]
            if not c: ok = False; break
            pts.append(rng.choice(c))
        if ok and len(lines) == 9: break
    NP = n + 1
    Lnew = [s[:] for s in L] + [pts[:]]
    for p, li in zip(pts, lines):
        Lnew[li].remove(p); Lnew[li].append(n)
    sigma = d_pt[:] + [n]          # sigma(x*) = l* = n  (mkplus convention)
    return NP, Lnew, sigma, pts, lines

def write(fn, NP, Lnew, sigma):
    with open(fn, "w") as f:
        f.write(f"{NP} 9\n")
        for s in Lnew: f.write(" ".join(map(str, s)) + "\n")
        for v in sigma: f.write(f"{v}\n")

if __name__ == "__main__":
    mode, seed, q, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    NP, Lnew, sigma, pts, lines = switch(mode, seed)
    if q >= 0:
        n = NP - 1
        sx = sigma[n]; sq = sigma[q]
        sigma[n] = sq; sigma[q] = n    # sigma(x*) <- delta(q), sigma(q) <- l*
    write(out, NP, Lnew, sigma)
    print("pts", pts, "lines", lines, "q", q, "sigma(x*)", sigma[NP-1])

"""Design D1 (card c1): W = h hyperbolic PG-line, switch lines L_j = delta(R_j) (j != k8), l* = sigma(R_k8),
x* on the 8 switch lines and l*. T = t.i. transversal of the regulus delta(h); p_j = T cap delta(R_j) (j != k8),
y8 = T cap delta(R_k8). sigma = delta, except sigma(R_k8) = l*, sigma(x*) = delta(y8), sigma(y8) = delta(R_k8).
Then W and Y = {p_j} + {y8} = T are both dominating (PG-lines), so both covering demands hold by construction.
usage: python3 mkD1.py seed count outprefix"""
import sys, random
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r3-d11D5/c1")
import geo
from geo import n, L, d_pt, pts, Lsets

def build_D1(h, t, k8):
    """h: sorted list of 9 point ids (hyperbolic); t: transversal line id; k8: index in h of R_k8."""
    R = list(h)
    Rk = R[k8]
    switch = [R[j] for j in range(9) if j != k8]
    lines = [list(s) for s in L] + [None]          # 586 lines (point lists), l* = index 585
    X = n
    p = {}
    for R_j in switch:
        lj = d_pt[R_j]
        cand = [q for q in L[lj] if q in Lsets[t]]
        assert len(cand) == 1
        p[R_j] = cand[0]
    y8 = [q for q in L[d_pt[Rk]] if q in Lsets[t]][0] if False else [q for q in L[t] if q in Lsets[d_pt[Rk]]][0]
    for R_j in switch:
        lj = d_pt[R_j]
        pos = lines[lj].index(p[R_j]); lines[lj][pos] = X
    lines[n] = sorted([p[R_j] for R_j in switch] + [X])
    sigma = list(d_pt) + [None]                    # sigma on old points, x* = index n
    sigma[Rk] = n                                  # sigma(R_k8) = l*
    sigma[X] = d_pt[y8]                            # sigma(x*) = delta(y8)
    sigma[y8] = d_pt[Rk]                           # sigma(y8) = delta(R_k8) (swap, unless y8 == R_k8)
    if y8 == Rk:
        sigma[X] = d_pt[Rk]
    return lines, sigma, y8

if __name__ == "__main__":
    seed, count, pref = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    hs = [sorted(h) for h in geo.hyp]
    best = None; results = []
    for it in range(count):
        h = rng.choice(hs); T = rng.choice(geo.transversals(h)); k8 = rng.randrange(9)
        lines, sigma, y8 = build_D1(h, T, k8)
        path = f"{pref}_{it}.in"
        geo.build(lines, sigma, path)
        out = geo.score(path)
        c = int(out.split("cost=")[1].split()[0])
        results.append((c, it, h, T, k8, y8))
        if best is None or c < best[0]:
            best = (c, it, h, T, k8, y8); print("new best", c, "it", it, "h", h, "T", T, "k8", k8, flush=True)
    results.sort()
    print("sorted costs (first 20):", [r[0] for r in results[:20]])
    print("median", results[len(results)//2][0], "max", results[-1][0])

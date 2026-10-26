"""Design D2 (card c1): as D1 but p_j = L_j cap t_{pi(j)} with the 9 transversals t_k of the regulus delta(h)
assigned by a random injection (different transversal per switch line).  sigma = delta except
sigma(R_k8) = l*, sigma(x*) = delta(R_k8).
usage: python3 mkD2.py seed count outdir"""
import sys, random, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r3-d11D5/c1")
import geo
from geo import n, L, d_pt, Lsets

def build_D2(h, k8, pi_seed):
    R = list(h); Rk = R[k8]
    switch = [R[j] for j in range(9) if j != k8]
    tr = geo.transversals(h)
    rr = random.Random(pi_seed); tt = tr[:]; rr.shuffle(tt)
    lines = [list(s) for s in L] + [None]; X = n
    p = {}
    for j, R_j in enumerate(switch):
        lj = d_pt[R_j]; t = tt[j]
        cand = [q for q in L[lj] if q in Lsets[t]]
        p[R_j] = cand[0]
    for R_j in switch:
        lj = d_pt[R_j]; pos = lines[lj].index(p[R_j]); lines[lj][pos] = X
    lines[n] = sorted([p[R_j] for R_j in switch] + [X])
    sigma = list(d_pt) + [None]
    sigma[Rk] = n; sigma[X] = d_pt[Rk]
    return lines, sigma

if __name__ == "__main__":
    seed, count, pref = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed); os.makedirs(pref, exist_ok=True)
    hs = [sorted(h) for h in geo.hyp]
    res = []
    for it in range(count):
        h = rng.choice(hs); k8 = rng.randrange(9); ps = rng.randrange(10**9)
        lines, sigma = build_D2(h, k8, ps)
        path = os.path.join(pref, f"d2_{seed}_{it}.in")
        geo.build(lines, sigma, path)
        c = int(geo.score(path).split("cost=")[1].split()[0])
        res.append((c, path, h, k8, ps))
    res.sort()
    print("best 10:", [r[0] for r in res[:10]], "median", res[len(res)//2][0])
    for r in res[:3]: print(r)

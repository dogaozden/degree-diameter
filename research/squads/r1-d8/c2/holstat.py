"""Holonomy statistic: for opposite point pairs (x,y), number of distinct Z_k sums over the q+1 geodesics (6 flags)."""
import random, sys, statistics
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c2')
import holo, gh
H = gh.load(5)
N = H.N
through = [[int(L) for L in H.through[p]] for p in range(N)]
lines = [[int(p) for p in H.lines[L]] for L in range(N)]

def stats(Fflag, k, nx=150, seed=0):
    """Fflag(p, L) -> Z_k (L line index). Returns mean distinct count and frac with all k values present."""
    rng = random.Random(seed)
    xs = rng.sample(range(N), nx)
    dist_counts, full = [], 0
    for x in xs:
        sums = {}
        for L1 in through[x]:
            s1 = Fflag(x, L1)
            for p1 in lines[L1]:
                if p1 == x: continue
                s1b = s1 - Fflag(p1, L1)
                for L2 in through[p1]:
                    if L2 == L1: continue
                    s2 = s1b + Fflag(p1, L2)
                    for p2 in lines[L2]:
                        if p2 == p1: continue
                        s2b = s2 - Fflag(p2, L2)
                        for L3 in through[p2]:
                            if L3 == L2: continue
                            s3 = s2b + Fflag(p2, L3)
                            for y in lines[L3]:
                                if y == p2: continue
                                v = (s3 - Fflag(y, L3)) % k
                                sums.setdefault(y, set()).add(v)
        for y, vs in sums.items():
            dist_counts.append(len(vs))
    mean = statistics.mean(dist_counts)
    frac_full = sum(1 for c in dist_counts if c == k) / len(dist_counts)
    return round(mean, 3), round(frac_full, 3), len(dist_counts)

if __name__ == '__main__':
    lam = holo.lam_table(H, holo.frames(H, 'first'))
    k = 5
    rules = {'sqclass': [0, 1, 2, 2, 1, 3], 'quad_sq': [0, 1, 4, 4, 1, 0], 'lin': [0, 1, 2, 3, 4, 0], 'cubic': [0, 1, 3, 2, 4, 0]}
    for name, Fv in rules.items():
        Ff = lambda p, L, Fv=Fv: Fv[lam[(p, L)]] % k
        print(name, 'mean distinct, frac all-5, #pairs:', stats(Ff, k, nx=60), flush=True)
    rng = random.Random(7)
    R = {}
    def Frand(p, L):
        key = (p, L)
        if key not in R: R[key] = rng.randrange(k)
        return R[key]
    print('random flags', 'mean distinct, frac all-5, #pairs:', stats(Frand, k, nx=60), flush=True)

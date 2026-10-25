import sys, time, itertools
sys.path.insert(0, '/tmp/claude-0/-home-user-degree-diameter/dc574623-c6c6-5598-9b3e-ade6117641a7/scratchpad')
from fam2 import closure, search
from fam import perm_mul

def affine_gens(p, r):   # Z_p x| <r>, r of order 3 mod p; points 0..p-1
    g1 = tuple((r*x) % p for x in range(p)); g2 = tuple((x+1) % p for x in range(p))
    return [g1, g2]

def abelian_types(a):
    def factor(n):
        f = {}; d = 2
        while d * d <= n:
            while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
            d += 1
        if n > 1: f[n] = f.get(n, 0) + 1
        return f
    def parts(n, maxp=None):
        if maxp is None: maxp = n
        if n == 0: yield []; return
        for k in range(min(n, maxp), 0, -1):
            for rest in parts(n - k, k): yield [k] + rest
    per = []
    for pr, ex in factor(a).items():
        per.append([[pr**k for k in pt] for pt in parts(ex)])
    res = []
    for combo in itertools.product(*per):
        mods = []
        for lst in combo: mods += lst
        res.append(tuple(sorted(mods)))
    return res

if __name__ == '__main__':
    t0 = time.time()
    jobs = []
    for p, r, alist in [(7, 2, range(75, 82)), (13, 3, [41, 42, 43]), (19, 7, [28, 29]), (31, 5, [17, 18]),
                        (37, 10, [15]), (43, 6, [13]), (61, 13, [9]), (67, 29, [8]), (79, 23, [7])]:
        base = closure(affine_gens(p, r))
        for a in alist:
            if p*3*a < 1561 or p*3*a > 1700: continue
            for mods in abelian_types(a):
                if len(mods) > 3: continue
                jobs.append((f"meta{p}_3", base, mods))
    print("jobs", len(jobs), flush=True)
    for name, base, mods in jobs:
        res = search(name, base, mods, maxM=3, maxc=2)
        if res: print("FOUND", res, flush=True)
    print("DONE", round(time.time()-t0,1), flush=True)

# Metacyclic groups G = <a,b | a^m=1, b^n=1, b a b^-1 = a^r>, order N = m*n, r^n = 1 mod m, gcd(r,m)=1.
# Only a family: the SmallGroups library is not installed for orders 1156..1200 in this sandbox.
# Writes groups/mc_<N>_<k>.txt (bicoset format: "N 0", then N rows, row g col h = index of g*h; (i,j) -> i*n+j).
import sys, os, math
from collections import Counter
OUT = "/home/user/degree-diameter/research/squads/bh5-r2/c3/grp2"
ORDERS = [int(x) for x in sys.argv[1].split(',')]
CAP = int(sys.argv[2])

def make(m, n, r):
    rp = [pow(r, j, m) for j in range(n)]
    def mulf(g, h):
        i, j = divmod(g, n); k, l = divmod(h, n)
        return ((i + k * rp[j]) % m) * n + (j + l) % n
    return mulf

def invariant(m, n, r):
    N = m * n; mulf = make(m, n, r)
    cnt = Counter(); 
    for x in range(N):
        o, y = 1, x
        while y != 0: y = mulf(y, x); o += 1
        cnt[o] += 1
    a, b = n, 1  # a = (1,0) -> index n ; b = (0,1) -> index 1
    center = sum(1 for x in range(N) if mulf(x, a) == mulf(a, x) and mulf(x, b) == mulf(b, x))
    return (tuple(sorted(cnt.items())), center)

for N in ORDERS:
    seen = {}
    for m in range(2, N + 1):
        if N % m: continue
        n = N // m
        if n < 2: continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, n, m) != 1: continue
            orb = {pow(r, t, m) for t in range(1, n + 1) if math.gcd(t, n) == 1}
            if min(orb) != r: continue
            inv_ = invariant(m, n, r)
            if inv_ in seen: continue
            seen[inv_] = (m, n, r)
    cands = sorted(seen.values(), key=lambda c: (c[2] == 1, -c[0], -c[2]))
    print(N, "classes", len(cands), flush=True)
    for k, (m, n, r) in enumerate(cands[:CAP]):
        mulf = make(m, n, r); N_ = m * n
        fn = os.path.join(OUT, "mc_%d_%d.txt" % (N, k))
        with open(fn, "w") as f:
            f.write("%d 0\n" % N_)
            for g in range(N_):
                f.write(" ".join(str(mulf(g, h)) for h in range(N_)) + "\n")
        with open(fn[:-4] + ".name", "w") as f:
            f.write("metacyclic m=%d n=%d r=%d abelian=%s\n" % (m, n, r, r == 1))

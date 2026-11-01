# Enumerate metacyclic groups G = <a,b | a^m, b^k = a^s, b a b^-1 = a^r> of order N in [LO,HI].
# One r per cyclic subgroup <r> of the units (w2 convention); s classes under s -> s + i*sigma and
# s -> u*s (u unit), sigma = sum_{j<k} r^j.  Abelian quotient order d*k, d = gcd(r-1,m); bound: d*k <= 309.
import sys, math
LO, HI, BOUND = int(sys.argv[1]), int(sys.argv[2]), 309
out = []
for N in range(LO, HI + 1):
    for m in range(1, N + 1):
        if N % m: continue
        k = N // m
        if k < 2: continue
        seen = set()
        for r in range(1, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            d = math.gcd(r - 1, m)
            if d * k > BOUND: continue
            sub = frozenset(pow(r, t, m) for t in range(k))
            if sub in seen: continue
            seen.add(sub)
            sigma = sum(pow(r, j, m) for j in range(k)) % m
            T = [s for s in range(m) if (s * (r - 1)) % m == 0]
            units = [u for u in range(1, m) if math.gcd(u, m) == 1]
            # union-find over T by s -> u*s and s -> s+sigma
            par = {s: s for s in T}
            def f(x):
                while par[x] != x:
                    par[x] = par[par[x]]; x = par[x]
                return x
            for s in T:
                for t in (sigma % m, ):
                    y = (s + t) % m
                    if y in par: par[f(s)] = f(y)
                for u in units:
                    y = (u * s) % m
                    if y in par: par[f(s)] = f(y)
            reps = sorted({f(s) for s in T})
            for s in reps:
                out.append((N, m, k, r, s, d, d * k))
with open(sys.argv[3], "w") as fh:
    for t in out: fh.write("%d %d %d %d %d %d %d\n" % t)
print(len(out), "candidates")

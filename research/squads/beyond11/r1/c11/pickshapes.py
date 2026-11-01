import math, sys
exec(open('cands.py').read().split('res = []')[0].replace('target = float(sys.argv[3])','target = float(sys.argv[3])'))
res = []
for p in primes:
    for fam, base in (("sl", p*(p*p-1)), ("psl", p*(p*p-1)//2)):
        for n in ns:
            if math.gcd(p, n) != 1: continue
            N = base*n
            if N > 1e9: break
            mu = N*math.exp(-W/N)
            if abs(mu-target)/target < 0.05:
                res.append((fam, p, n, N, mu))
targets = [("n=1", None), ("n~p/10", 0.1), ("n~p/2", 0.5), ("n~p", 1.0), ("n~4p", 4.0)]
for fam in ("sl", "psl"):
    for name, r in targets:
        cand = [x for x in res if x[0]==fam]
        if r is None:
            c = max([x for x in cand if x[2]==1], key=lambda x:x[1], default=None)
        else:
            c = min([x for x in cand if x[2]>1], key=lambda x: abs(x[2]/x[1]-r)+ (0 if x[1]>0 else 9), default=None)
            # prefer mu close to target too
        if c: print(fam, name, "p=%d n=%d N=%d mu=%.3f n/p=%.3f" % (c[1], c[2], c[3], c[4], c[2]/c[1]))

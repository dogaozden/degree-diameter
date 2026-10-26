import sys, random, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
q = 3; G = geometry(q); N = G["N"]; Q1 = G["Q1"]
s1, s2 = geo_sigmas(G)
m = 20
print("sigma sanity: bijective", len(set(s1)) == N and len(set(s2)) == N)
random.seed(7)
res = []
t0 = time.time()
for trial in range(int(sys.argv[1])):
    i1, i2, iinf = random.randrange(1, m), random.randrange(1, m), random.randrange(1, m)
    iota = [0, i1, i2, iinf]
    hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
    mb = random.randrange(1, m)
    c = evaluate(q, m, [s1, s2], [[1] * N, [mb] * N], hv, tag="ft")
    res.append((c, iota, mb))
    print(trial, "iota", iota, "mv2", mb, "fullcost", c, flush=True)
res.sort(key=lambda r: (r[0] is None, r[0]))
print("best", res[:5], "time %.1f" % (time.time() - t0))

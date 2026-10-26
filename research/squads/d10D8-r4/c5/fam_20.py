import sys, random, time, math
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
q = 3; G = geometry(q); N = G["N"]; Q1 = G["Q1"]
m = int(sys.argv[1]); n = int(sys.argv[2]); random.seed(int(sys.argv[3])); sh = int(sys.argv[4])
rp, lr = G["rank_p"], G["line_of_rank"]
s1 = [lr[rp[p]] for p in range(N)]; s2 = [lr[(rp[p] + sh) % N] for p in range(N)]
units = [u for u in range(1, m) if math.gcd(u, m) == 1]
best = []; t0 = time.time(); found = None
for trial in range(n):
    iota = [0] + [random.randrange(1, m) for _ in range(3)]
    hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
    ma = random.choice(units); mb = random.randrange(1, m)
    c = evaluate(q, m, [s1, s2], [[ma] * N, [mb] * N], hv, tag="f20")
    best.append((c, iota, ma, mb))
    if c == 0:
        found = (iota, ma, mb); print("FOUND", found, flush=True); break
best.sort(key=lambda r: (r[0] is None, r[0]))
print("m", m, "sh", sh, "found", found, "best3", best[:3], "n", len(best), "time %.1f" % (time.time() - t0), flush=True)

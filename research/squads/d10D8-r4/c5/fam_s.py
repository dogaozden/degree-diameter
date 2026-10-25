import sys, random, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
q = 3; G = geometry(q); N = G["N"]; Q1 = G["Q1"]
m = 20
random.seed(int(sys.argv[2]))
rp, lr = G["rank_p"], G["line_of_rank"]
best = []
t0 = time.time()
for trial in range(int(sys.argv[1])):
    sh = random.choice([N // 3, N // 2, N // 4, N // 5, N // 7, N // 11, N // 13])
    s1 = [lr[rp[p]] for p in range(N)]
    s2 = [lr[(rp[p] + sh) % N] for p in range(N)]
    iota = [0] + [random.randrange(1, m) for _ in range(3)]
    iota[1] = random.randrange(1, m)
    hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
    mb = random.randrange(1, m); ma = random.choice([1, 3, 7, 9, 11, 13, 17, 19])
    c = evaluate(q, m, [s1, s2], [[ma] * N, [mb] * N], hv, tag="fs")
    best.append((c, sh, iota, ma, mb))
    if c == 0:
        print("FOUND", c, "shift", sh, "iota", iota, "mv1", ma, "mv2", mb, flush=True)
        break
best.sort(key=lambda r: (r[0] is None, r[0]))
print("best5", best[:5], "n", len(best), "time %.1f" % (time.time() - t0), flush=True)

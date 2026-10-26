# generate candidate specs for d09 (N in 2486..2900), capped sample for the proxy stage
import json, math, itertools, random, sys
LO, HI = 2486, 2900
rng = random.Random(7)
def ordmod(r, m):
    x, k = r % m, 1
    while x != 1 % m:
        x = x * r % m; k += 1
        if k > 10000: return None
    return k
# small nonabelian factors X (order <= 60), chosen families
X = [("dih 3", 6), ("dih 4", 8), ("dih 5", 10), ("dih 6", 12), ("dih 7", 14), ("dih 9", 18), ("dih 10", 20),
     ("dih 12", 24), ("dih 15", 30), ("meta 7 3 2", 21), ("meta 5 4 2", 20), ("meta 13 3 3", 39),
     ("meta 11 5 3", 55), ("meta 7 6 3", 42), ("meta 13 4 5", 52), ("sl2 3", 24), ("perm 4 1,2,3,0 ; 1,0,2,3", 24),
     ("perm 4 1,2,0,3 ; 1,0,3,2", 12), ("agl1 5", 20), ("agl1 7", 42), ("psl2 5", 60), ("heis 3", 27)]
# metacyclic Y, grouped by order, faithful (ord r = k), gcd(r-1,m) <= 2, k >= 3, order in [41, HI]
Ybyorder = {}
for m in range(3, HI + 1):
    for k in range(3, HI // m + 1):
        if m * k < 41: continue
        for r in range(2, m):
            if math.gcd(r - 1, m) > 2 or math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            if ordmod(r, m) != k: continue
            Ybyorder.setdefault(m * k, []).append(f"meta {m} {k} {r}")
print("meta orders", len(Ybyorder), file=sys.stderr)
specs = []
for xs, xo in X:
    lo, hi = -(-LO // xo), HI // xo
    pool = [(o, s) for o in range(lo, hi + 1) for s in Ybyorder.get(o, [])]
    pool = [(xo * o, f"{xs} x {s}") for o, s in pool if xo * o >= LO]
    pool = [(N, s) for N, s in pool if N <= HI]
    rng.shuffle(pool)
    print(xs, "pool", len(pool), file=sys.stderr)
    specs += [(s, N) for N, s in pool[:9]]
# semidirect Z_p^2 x| Z_k with a matrix of order s | k, s >= 2, deduplicated by (trace, det, order)
def mul(A, B, p):
    a, b, c, d = A; e, f, g, h = B
    return ((a*e + b*g) % p, (a*f + b*h) % p, (c*e + d*g) % p, (c*f + d*h) % p)
def mord(M, p):
    I = (1, 0, 0, 1); X_ = M; k = 1
    while X_ != I:
        X_ = mul(X_, M, p); k += 1
        if k > 500: return None
    return k
semi = []
for p in [3, 5, 7, 11, 13, 17, 19, 23]:
    mats = {}
    for M in itertools.product(range(p), repeat=4):
        a_, b_, c_, d_ = M
        if (a_*d_ - b_*c_) % p == 0: continue
        s = mord(M, p)
        if s is None or s < 2: continue
        mats.setdefault(((a_+d_) % p, (a_*d_-b_*c_) % p, s), M)
    for k in range(3, 3000):
        if not (LO <= p*p*k <= HI): continue
        for key, M in mats.items():
            if k % key[2] == 0:
                semi.append((f"semi {p} {k} {M[0]} {M[1]} {M[2]} {M[3]}", p*p*k))
    print("p", p, "mats", len(mats), file=sys.stderr)
random.Random(3).shuffle(semi)
print("semi total", len(semi), file=sys.stderr)
specs += semi[:70]
print("specs", len(specs), file=sys.stderr)
json.dump(specs, open("/home/user/degree-diameter/research/squads/b48/r3/d09/specs_all.json", "w"))

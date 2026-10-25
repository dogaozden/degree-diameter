"""c5: geometric labels for H(4) over GF(4) (hexgen2 encoding: element a0 + 2*a1 means a0 + a1*x, x^2 = x + 1)."""
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *

def gf4_mul(a, b):
    a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
    c0 = (a0 * b0 + a1 * b1) & 1
    c1 = (a0 * b1 + a1 * b0 + a1 * b1) & 1
    return c0 + 2 * c1
GF4_INV = {x: next(y for y in range(1, 4) if gf4_mul(x, y) == 1) for x in range(1, 4)}

def geometry4():
    q = 4; H = load_hex(q); N = H["N"]; Q1 = H["Q1"]; pl = H["pl"]; co = H["coords"]
    order_p = sorted(range(N), key=lambda p: co[p])
    rank_p = [0] * N
    for r, p in enumerate(order_p): rank_p[p] = r
    lines_pts = [pl[l * Q1:(l + 1) * Q1] for l in range(N)]
    keys = []
    for l in range(N):
        pts = sorted(lines_pts[l], key=lambda p: co[p]); keys.append((co[pts[0]], co[pts[1]]))
    order_l = sorted(range(N), key=lambda l: keys[l])
    rank_l = [0] * N
    for r, l in enumerate(order_l): rank_l[l] = r
    tlab = {}
    for l in range(N):
        pts = sorted(lines_pts[l], key=lambda p: co[p])
        a, b = co[pts[0]], co[pts[1]]
        for k in range(Q1):
            v = co[pl[l * Q1 + k]]
            sol = None
            for i in range(7):
                for j in range(7):
                    if i == j: continue
                    det = gf4_mul(a[i], b[j]) ^ gf4_mul(a[j], b[i])
                    if det:
                        iv = GF4_INV[det]
                        al = gf4_mul(gf4_mul(v[i], b[j]) ^ gf4_mul(b[i], v[j]), iv)
                        be = gf4_mul(gf4_mul(a[i], v[j]) ^ gf4_mul(v[i], a[j]), iv)
                        sol = (al, be); break
                if sol: break
            al, be = sol
            if be == 0: t = 4
            else: t = gf4_mul(al, GF4_INV[be])
            tlab[(l, k)] = t
    return dict(H=H, N=N, Q1=Q1, pl=pl, co=co, rank_p=rank_p, rank_l=rank_l, line_of_rank=order_l, tlab=tlab)

if __name__ == "__main__":
    import random, time
    # sanity: field axioms for GF(4) tables
    assert all(gf4_mul(a, GF4_INV[a]) == 1 for a in range(1, 4))
    G = geometry4(); N = G["N"]; Q1 = G["Q1"]
    print("labels used", sorted(set(G["tlab"].values())), "lines", N, "Q1", Q1)
    m = int(sys.argv[1]); n = int(sys.argv[2]); random.seed(int(sys.argv[3]))
    rp, lr = G["rank_p"], G["line_of_rank"]
    import math
    units = [u for u in range(1, m) if math.gcd(u, m) == 1]
    best = []; t0 = time.time(); found = None
    for trial in range(n):
        sh = random.choice([N // 3, N // 2, N // 4, N // 5, N // 7, N // 11, N // 13, N // 9])
        s1 = [lr[rp[p]] for p in range(N)]
        s2 = [lr[(rp[p] + sh) % N] for p in range(N)]
        iota = [random.randrange(0, m) for _ in range(5)]
        hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
        ma = random.choice(units); mb = random.randrange(1, m)
        c = evaluate(4, m, [s1, s2], [[ma] * N, [mb] * N], hv, tag="g4m%d" % m)
        best.append((c, sh, iota, ma, mb))
        print(trial, c, "%.1fs" % (time.time() - t0), flush=True)
        if c == 0:
            found = (sh, iota, ma, mb); break
    best.sort(key=lambda r: (r[0] is None, r[0]))
    print("q4 m", m, "found", found, "best3", best[:3], "n", len(best), flush=True)

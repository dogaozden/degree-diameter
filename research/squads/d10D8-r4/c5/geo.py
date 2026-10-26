"""c5 geometric labels for H(q), q prime: coordinates from hexgen2 (normalized PG(6,q) vectors)."""
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *

def geometry(q):
    H = load_hex(q); N = H["N"]; Q1 = H["Q1"]; pl = H["pl"]; co = H["coords"]
    # lex rank of points by normalized coordinates
    order_p = sorted(range(N), key=lambda p: co[p])
    rank_p = [0] * N
    for r, p in enumerate(order_p): rank_p[p] = r
    # canonical line key: lex-smallest two points' coordinates; lines ranked by key
    lines_pts = [pl[l * Q1:(l + 1) * Q1] for l in range(N)]
    keys = []
    for l in range(N):
        pts = sorted(lines_pts[l], key=lambda p: co[p])
        keys.append((co[pts[0]], co[pts[1]]))
    order_l = sorted(range(N), key=lambda l: keys[l])
    rank_l = [0] * N
    for r, l in enumerate(order_l): rank_l[l] = r
    line_of_rank = order_l
    # t-labels: for line l with basis (a, b) = two lex-smallest points, t(p) in {0..q-1, q=inf}
    tlab = {}   # (l, k) -> t
    for l in range(N):
        pts = sorted(lines_pts[l], key=lambda p: co[p])
        a, b = co[pts[0]], co[pts[1]]
        for k in range(Q1):
            p = pl[l * Q1 + k]; v = co[p]
            # solve v = al*a + be*b over GF(q), q prime: find two coordinates with invertible minor
            sol = None
            for i in range(7):
                for j in range(7):
                    if i == j: continue
                    det = (a[i] * b[j] - a[j] * b[i]) % q
                    if det:
                        inv = pow(det, q - 2, q)
                        al = ((v[i] * b[j] - v[j] * b[i]) * inv) % q
                        be = ((a[i] * v[j] - a[j] * v[i]) * inv) % q
                        sol = (al, be); break
                if sol: break
            al, be = sol
            if be == 0: t = q          # p proportional to a: infinity
            else: t = (al * pow(be, q - 2, q)) % q
            tlab[(l, k)] = t
    return dict(H=H, N=N, Q1=Q1, pl=pl, co=co, rank_p=rank_p, rank_l=rank_l, line_of_rank=line_of_rank, tlab=tlab)

def geo_sigmas(G, shift_frac=3):
    N = G["N"]; rp = G["rank_p"]; lr = G["line_of_rank"]
    s1 = [lr[rp[p]] for p in range(N)]
    s2 = [lr[(rp[p] + N // shift_frac) % N] for p in range(N)]
    return s1, s2

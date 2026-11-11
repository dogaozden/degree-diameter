# builds list_semi.tsv: Z_p^2 x| Z_k (matrix M of order dividing k, several classes) and heis x cyc candidates
import random, itertools
random.seed(5)
rows = []
def matmul(A, B, p):
    return ((A[0]*B[0]+A[1]*B[2])%p, (A[0]*B[1]+A[1]*B[3])%p, (A[2]*B[0]+A[3]*B[2])%p, (A[2]*B[1]+A[3]*B[3])%p)
def mpow(M, e, p):
    R = (1,0,0,1)
    for _ in range(e): R = matmul(R, M, p)
    return R
def order(M, p):
    R = M; o = 1
    while R != (1,0,0,1):
        R = matmul(R, M, p); o += 1
        if o > 10000: return None
    return o
ranges = {3: range(277, 301), 5: range(100, 109), 7: range(51, 56), 11: range(21, 23), 13: [15], 17: [9], 19: [7], 23: [5], 29: [3]}
for p, ks in ranges.items():
    seen = set()
    for _ in range(4000):
        M = tuple(random.randrange(p) for _ in range(4))
        if (M[0]*M[3]-M[1]*M[2]) % p == 0: continue
        o = order(M, p)
        if o is None or o < 2: continue
        tr = (M[0]+M[3]) % p; det = (M[0]*M[3]-M[1]*M[2]) % p
        key = (o, tr, det)
        if key in seen: continue
        seen.add(key)
        for k in ks:
            if k % o == 0:
                rows.append(("grp", "semi_p%d_k%d_o%d_t%d_d%d" % (p, k, o, tr, det), "semi %d %d %d %d %d %d" % (p, k, *M)))
# heisenberg x cyclic (N = p^3 * n in range)
for n in range(93, 101): rows.append(("grp", "heis3_x%d" % n, "heis 3 x cyc %d" % n))
rows.append(("grp", "heis5_x20", "heis 5 x cyc 20")); rows.append(("grp", "heis5_x21", "heis 5 x cyc 21"))
with open("list_semi.tsv", "w") as f:
    for r in rows: f.write("\t".join(r) + "\n")
print(len(rows))
for r in rows[:5]: print(r)

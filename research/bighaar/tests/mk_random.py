"""random generator set with s_0 = e for G = SL/PSL(2,p) x Z_n, haar_gen3 format.  usage: mk_random.py d D fam p n seed"""
import sys, random
d, D, fam, p, n, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
random.seed(seed)
order = p * (p * p - 1) // (2 if fam == "psl" else 1) * n
print("%d %d %s %d n %d N %d" % (d, D, fam, p, n, order))
print("0 mat(1,0,0,1) z=0")
seen = {((1, 0, 0, 1), 0)}
while len(seen) < d:
    a, b, c = (random.randrange(p) for _ in range(3))
    if a == 0: continue
    dd = (1 + b * c) * pow(a, p - 2, p) % p
    m = (a, b, c, dd)
    if fam == "psl":
        f = a if a else c
        if f > (p - 1) // 2: m = tuple((-x) % p for x in m)
    z = random.randrange(n)
    if (m, z) in seen: continue
    seen.add((m, z)); print("0 mat(%d,%d,%d,%d) z=%d" % (m + (z,)))

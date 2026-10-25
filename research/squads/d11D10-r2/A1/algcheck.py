# Check the group identities behind the AFROB/AR pairings on random matrices of GL(2,243).
# GF(243) = GF(3)[x]/(x^5+2x+1), elements are integers sum c_i 3^i (as in haar_sym). x^5 = x + 2 mod 3.
import random
def vec(n): return [(n // 3**i) % 3 for i in range(5)]
def num(v): return sum((v[i] % 3) * 3**i for i in range(5))
def mul(a, b):
    va, vb = vec(a), vec(b); p = [0] * 9
    for i in range(5):
        for j in range(5): p[i + j] += va[i] * vb[j]
    for d in range(8, 4, -1):
        c = p[d] % 3; p[d] = 0; p[d - 4] += c; p[d - 5] += 2 * c
    return num(p[:5])
def add(a, b): return num([(x + y) % 3 for x, y in zip(vec(a), vec(b))])
def neg(a): return num([(-x) % 3 for x in vec(a)])
INV = {}
for a in range(1, 243):
    for b in range(1, 243):
        if mul(a, b) == 1: INV[a] = b; break
assert len(INV) == 242, "not a field"
def mm(X, Y):
    a, b, c, d = X; e, f, g, h = Y
    return (add(mul(a, e), mul(b, g)), add(mul(a, f), mul(b, h)), add(mul(c, e), mul(d, g)), add(mul(c, f), mul(d, h)))
def det(X):
    a, b, c, d = X; return add(mul(a, d), neg(mul(b, c)))
def frob(a, j):   # a -> a^(3^j), i.e. the cube map applied j times
    for _ in range(j): a = mul(a, mul(a, a))
    return a
def norm(X):   # projective normal form (mod scalars)
    e = next(t for t in X if t); s = INV[e]
    return tuple(mul(s, t) for t in X)
H = (0, 1, 2, 0)                      # h = mat(0,1,2,0), entries in GF(3)
Hi = (0, 2, 1, 0)                     # h^-1 (det h = 1)
assert mm(H, Hi) == (1, 0, 0, 1)
def phi(j, M):   # alpha_Q(M) = h * Frob^j(M) * h^-1 (entrywise Frobenius)
    F = tuple(frob(t, j) for t in M)
    return norm(mm(mm(H, F), Hi))
def papply(j, k, M):
    for _ in range(k): M = phi(j, M)
    return M
random.seed(12345)
tests = []
while len(tests) < 40:
    M = tuple(random.randrange(243) for _ in range(4))
    if det(M) != 0: tests.append(norm(M))
ok = {"phi4^9 == phi1 (AR=6 of AFROB=1 vs AFROB=4 AR=2)": 0,
      "phi3^7 == phi1 (AR=7 of AFROB=1 vs AFROB=3 AR=2)": 0,
      "phi1^7 == phi2 (AFROB=2 AR=7 vs AFROB=1 AR=2)": 0,
      "phi1^9 == phi4 (AFROB=4 AR=6 vs AFROB=1 AR=2)": 0,
      "phi1^10 == id (order of phi_1; sanity)": 0}
for M in tests:
    ok["phi4^9 == phi1 (AR=6 of AFROB=1 vs AFROB=4 AR=2)"] += papply(4, 9, M) == phi(1, M)
    ok["phi3^7 == phi1 (AR=7 of AFROB=1 vs AFROB=3 AR=2)"] += papply(3, 7, M) == phi(1, M)
    ok["phi1^7 == phi2 (AFROB=2 AR=7 vs AFROB=1 AR=2)"] += papply(1, 7, M) == phi(2, M)
    ok["phi1^9 == phi4 (AFROB=4 AR=6 vs AFROB=1 AR=2)"] += papply(1, 9, M) == phi(4, M)
    ok["phi1^10 == id (order of phi_1; sanity)"] += papply(1, 10, M) == M
for k, v in ok.items(): print("%-60s %d / %d" % (k, v, len(tests)))
print("phi_1 has order 10 on the sample (phi^10 = id):", all(papply(1, 10, M) == M for M in tests))

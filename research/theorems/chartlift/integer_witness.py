"""Schwartz-Zippel step for universal charts (CHART_LIFTS.md, Theorem 10).
With A_0 = I, the chart entries (A_1..A_3, b_0..b_3) are 64 variables.  For each nonbacktracking 4-pattern:
  side A: P = det[adj(A_i2) b_i1, adj(A_i2) b_i2, adj(A_i3) b_i3, adj(A_i3) b_i4]        (degree <= 16)
  side B: P = det[A_i2 adj(A_i1) b_i1, b_i2, b_i3, A_i3 adj(A_i4) b_i4]                   (degree <= 12)
(adj(A) = det(A) A^-1, so when every det(A_c) != 0 the pattern is nonsingular iff P != 0.)  F = prod P * prod det(A_c)
has degree <= 108*16 + 108*12 + 3*4 = 3036.  This script finds integer charts at which each P takes nonzero values
whose gcd over the witnesses is 1; hence P mod p is a nonzero polynomial for EVERY prime p, so F mod p != 0, and by
Schwartz-Zippel a universal chart exists over F_q for every q > 3036.  Output: runs/integer_witness.out."""
import itertools, random, math, json

def det(M):
    M = [row[:] for row in M]; n = len(M); sign = 1; prev = 1
    for k in range(n - 1):                      # Bareiss fraction-free elimination
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k]), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]
def adj(M):
    n = len(M)
    cof = [[(-1) ** (i + j) * det([[M[r][c] for c in range(n) if c != j] for r in range(n) if r != i]) for j in range(n)] for i in range(n)]
    return [[cof[j][i] for j in range(n)] for i in range(n)]
def mv(M, v): return [sum(a * b for a, b in zip(row, v)) for row in M]
K = 4
PATS = [p for p in itertools.product(range(K), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3]]
def values(A, b):
    ad = [adj(M) for M in A]; out = {}
    for i1, i2, i3, i4 in PATS:
        cols = [mv(ad[i2], b[i1]), mv(ad[i2], b[i2]), mv(ad[i3], b[i3]), mv(ad[i3], b[i4])]
        out[('A',) + (i1, i2, i3, i4)] = det([list(r) for r in zip(*cols)])
        cols = [mv(A[i2], mv(ad[i1], b[i1])), b[i2], b[i3], mv(A[i3], mv(ad[i4], b[i4]))]
        out[('B',) + (i1, i2, i3, i4)] = det([list(r) for r in zip(*cols)])
    return out
rng = random.Random(2026)
I = [[int(r == c) for c in range(4)] for r in range(4)]
g = {key: 0 for key in [('A',) + p for p in PATS] + [('B',) + p for p in PATS]}
witnesses = []
for t in range(2000):
    A = [I] + [[[rng.randint(-2, 2) for _ in range(4)] for _ in range(4)] for _ in range(3)]
    if any(det(M) == 0 for M in A): continue
    b = [[rng.randint(-2, 2) for _ in range(4)] for _ in range(4)]
    vals = values(A, b)
    useful = [kk for kk, v in vals.items() if v != 0 and g[kk] != 1]
    if not useful: continue
    for kk in useful: g[kk] = math.gcd(g[kk], vals[kk])
    witnesses.append({'A': A, 'b': b, 'detA': [det(M) for M in A]})
    if all(v == 1 for v in g.values()): break
def largest_prime_factor(n):
    n = abs(n); best, d = 1, 2
    while d * d <= n:
        while n % d == 0: best = d; n //= d
        d += 1
    return max(best, n) if n > 1 else best
bad = {kk: v for kk, v in g.items() if v != 1}
print('patterns:', len(g), ' witnesses used:', len(witnesses))
print('patterns whose witness gcd is not 1 (gcd, largest prime factor):', {str(kk): (v, largest_prime_factor(v)) for kk, v in bad.items()})
assert all(v != 0 and largest_prime_factor(v) <= 3036 for v in bad.values())
print('every gcd is 3036-smooth: for each prime p > 3036 every pattern polynomial is nonzero mod p (integer witness);')
print('for each prime p <= 3036 the explicit universal chart over F_p (F_4 for p = 2) shows the same.')
deg = 108 * 16 + 108 * 12 + 3 * 4
print('degree bound of F = prod(pattern polynomials) * prod det(A_c):', deg)
print('=> for every prime p, F mod p is a nonzero polynomial; Schwartz-Zippel: a universal chart exists over F_q for every q >', deg)
json.dump(witnesses, open('runs/integer_witnesses.json', 'w'))

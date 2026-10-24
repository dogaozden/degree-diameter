# Light scan (no haar_sym): k = 11 single-orbit family, S = one alpha-orbit, alpha = conj by g (order 11) x (z -> r z).
# N = |G| = |PSL(2,p)| * n; W = 1111111111; lam = W/N; mu = N e^-lam; clumps: non-fixed orbits ~ (N-F)/11 * e^-lam,
# fixed elements (F = |C(g)| incl. e, z-part trivial when r = 1 mod no prime) each uncovered w.p. e^-(lam/11).
import math
W = 1111111111
def primes_ok(n, k=11):
    f = {}; x = n; d = 2
    while d * d <= x:
        while x % d == 0: f[d] = f.get(d, 0) + 1; x //= d
        d += 1
    if x > 1: f[x] = f.get(x, 0) + 1
    return all((p - 1) % k == 0 for p in f), f
def isprime(p): return p > 1 and all(p % q for q in range(2, int(p ** .5) + 1))
rows = []
for p in range(5, 400):
    if not isprime(p) or (p % 11 not in (1, 10) and p != 11): continue
    G0 = p * (p * p - 1) // 2
    cen = (p - 1) // 2 if ((p - 1) // 2) % 11 == 0 else (p + 1) // 2
    for n in range(1, 40000):
        N = G0 * n
        if N < 70e6 or N > 85e6: continue
        ok, f = primes_ok(n)
        if not ok: continue
        lam = W / N; mu = N * math.exp(-lam)
        F = cen  # fixed elements of alpha (incl. e), assuming gcd(r-1, n) = 1
        muA = (N - F) / 11 * math.exp(-lam) + F * math.exp(-lam / 11)
        rows.append((2 * N, p, n, F, round(mu, 2), round(muA, 2), round(math.exp(-muA), 6)))
rows.sort(key=lambda r: -r[1 - 1 + 0] if False else r[0])
print("vertices  p  n  |Fix| mu  mu_A  P0(poisson)")
for r in rows: print(*r)

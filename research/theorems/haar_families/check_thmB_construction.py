"""Check the algebra of the proof of Theorem 3.2(b): for p = 1 mod 4 and primes q > p, build
beta = q u + (P - q^2) i + q v j + q w k with P = p^(L0/2), u^2+v^2+w^2 = 2P - q^2, u odd; verify N(beta) = p^L0,
beta = 1 mod 2, and psi(beta) = c psi(i) mod q (as matrices, with the splitting x^2 + y^2 = -1 used by lps_haar)."""
import math, sys
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5) + 1))
def three_squares(n):
    a = 0
    while a * a <= n:
        r = n - a * a; b = 0
        while b * b <= r:
            c2 = r - b * b; c = math.isqrt(c2)
            if c * c == c2: return a, b, c
            b += 1
        a += 1
    return None
def psi(b, q, x, y):
    a0, a1, a2, a3 = b
    return [(a0 + a1*x + a3*y) % q, (-a1*y + a2 + a3*x) % q, (-a1*y - a2 + a3*x) % q, (a0 - a1*x - a3*y) % q]
bad = 0; n = 0
for p in [5, 13, 17, 29, 37]:
    for q in range(p + 1, 1000):
        if not isprime(q): continue
        x = y = None
        for a in range(q):
            for b in range(q):
                if (a*a + b*b + 1) % q == 0: x, y = a, b; break
            if x is not None: break
        L = 0
        while not 2 * p**(L // 2) > q * q: L += 2
        P = p**(L // 2); n1 = 2 * P - q * q
        t = three_squares(n1); odd = [s for s in t if s % 2]; even = [s for s in t if s % 2 == 0]
        if len(odd) != 1: bad += 1; print('parity fail', p, q); continue
        u, v, w = odd[0], even[0], even[1]
        beta = (q * u, P - q * q, q * v, q * w)
        ok = sum(c * c for c in beta) == p**L and beta[0] % 2 == 1 and all(c % 2 == 0 for c in beta[1:])
        M, Mi = psi(beta, q, x, y), psi((0, 1, 0, 0), q, x, y)
        c = M[0] * pow(Mi[0], q - 2, q) % q if Mi[0] else M[1] * pow(Mi[1], q - 2, q) % q
        ok = ok and all((M[t] - c * Mi[t]) % q == 0 for t in range(4)) and c % q != 0
        n += 1
        if not ok: bad += 1; print('FAIL', p, q, beta)
print(f'{n} cases (p = 5, 13, 17, 29, 37; p < q < 1000), {bad} failures')

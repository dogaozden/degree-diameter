# enumerate groups G = (SL|PSL|PGL)(2,q) x Z_n with q prime (q>=5) and N = |G| in (lo, hi]; prints N, 2N, mu
import math, sys
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def W(d, D):
    return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
lo, hi = float(sys.argv[1]), float(sys.argv[2])
w = W(5, 14)
out = []
for q in range(5, 400):
    if not isprime(q): continue
    for fam, base in (("sl", q * (q * q - 1)), ("psl", q * (q * q - 1) // 2), ("pgl", q * (q * q - 1))):
        for n in range(1, 2000):
            N = base * n
            if N > hi: break
            if N <= lo or math.gcd(q, n) != 1: continue
            if n > 1 and not isprime(n): continue
            mu = N * math.exp(-w / N)
            out.append((N, fam, q, n, mu))
out.sort()
for N, fam, q, n, mu in out:
    print(f"{fam} {q} {n} N={N} 2N={2*N} mu={mu:.2f}")

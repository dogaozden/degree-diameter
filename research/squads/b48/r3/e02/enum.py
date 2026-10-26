# Enumerate Frobenius groups Z_p x| Z_k (p prime, k | p-1, k>=3, r of order exactly k) with order in a range.
import sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
def isprime(n):
    return n > 1 and all(n % q for q in range(2, int(n**0.5) + 1))
def order(r, p):
    x, o = r % p, 1
    while x != 1:
        x = x * r % p; o += 1
    return o
out = []
for p in range(3, hi + 1):
    if not isprime(p):
        continue
    for k in range(3, (p - 1) + 1):
        if (p - 1) % k or p * k < lo or p * k > hi:
            continue
        # primitive root
        g = next(g for g in range(2, p) if order(g, p) == p - 1) if p > 2 else 1
        r = pow(g, (p - 1) // k, p)
        assert order(r, p) == k
        out.append((p * k, p, k, r))
for N, p, k, r in sorted(out):
    print(f"meta:{p}:{k}:{r} N={N} p={p} k={k}")

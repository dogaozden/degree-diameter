# enumerate Q x (Z_p x|_r Z_k) Frobenius with k odd in 9..31, N = |Q| p k in [47737, 49200]
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
Qs = {"psl 3": 12, "sl 3": 24, "meta 7 3 2": 21, "meta 13 3 3": 39, "meta 19 3 7": 57}
pf = lambda k: [f for f in range(2, k + 1) if k % f == 0 and isprime(f)]
out = []
for k in range(9, 32, 2):
    for p in range(3, 60000):
        if (p - 1) % k or not isprime(p):
            continue
        for Qn, qo in Qs.items():
            N = qo * p * k
            if not (47737 <= N <= 49200):
                continue
            rr = None
            for r in range(2, p):
                if pow(r, k, p) == 1 and all(pow(r, k // f, p) != 1 for f in pf(k)):
                    rr = r; break
            if rr: out.append((N, Qn, p, k, rr))
for row in sorted(out): print(*row)

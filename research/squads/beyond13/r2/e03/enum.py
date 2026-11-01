import math, sys
d, D = 6, 13
W = 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def mu(N): return N * math.exp(-W / N)
out = []
for k in [19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]:
    for p in range(1, 2000000):
        m = p
        if (p - 1) % k: continue
        N = m * k
        if N < 20200000 or N > 21600000: continue
        if not isprime(p): continue
        out.append((N, k, p, round(mu(N), 2), p % 3 == 1))
out.sort()
for row in out: print("N=%d k=%d p=%d mu=%s p1mod3=%s" % row)
print("W", W, "mu(20213544)", round(mu(20213544),2))

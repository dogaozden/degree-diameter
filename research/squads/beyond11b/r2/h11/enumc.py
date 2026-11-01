import sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
def order_mod(r, m):
    x, o = r % m, 1
    while x != 1:
        x = x * r % m; o += 1
    return o
out = []
for p in range(3, hi + 1):
    if not is_prime(p): continue
    for k in range(3, hi // p + 1, 2):   # odd k, Frobenius
        N = p * k
        if N < lo or N > hi: continue
        if (p - 1) % k: continue
        rs = [r for r in range(2, p) if order_mod(r, p) == k]
        if rs: out.append((N, p, k, rs[0]))
out.sort(reverse=True)
for N, p, k, r in out: print(N, p, k, r)

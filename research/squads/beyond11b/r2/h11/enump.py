import sys
sys.argv += []
def is_prime(n):
    return n >= 2 and all(n % i for i in range(2, int(n**0.5) + 1))
def order_mod(r, m):
    x, o = r % m, 1
    while x != 1: x = x * r % m; o += 1
    return o
out = []
# SL(2,3) x Frobenius-type F of order f in [31,85]; also SL(2,3) x cyc n
for f in range(31, 86):
    out.append((24*f, f"sl2 3 x cyc {f}"))
    for p in range(3, f+1):
        if f % p or not is_prime(p): continue
        k = f // p
        if k < 3 or k % 2 == 0 or (p-1) % k: continue
        rs = [r for r in range(2, p) if order_mod(r, p) == k]
        if rs: out.append((24*f, f"sl2 3 x meta {p} {k} {rs[0]}"))
out = [o for o in out if 738 <= o[0] <= 2044]
out.sort(reverse=True)
for N, s in out: print(N, s.replace(' ', '_'))

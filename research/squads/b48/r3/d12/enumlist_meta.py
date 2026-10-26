import math
def order_mod(r, m):
    if m == 1: return 1
    x, t = r % m, 1
    while x != 1 % m:
        x = x * r % m; t += 1
    return t
out = []
for m in range(2, 5601):
    for k in range(2, 5601 // m + 1):
        N = m * k
        if N < 4972 or N > 5600 or N % 2: continue
        if math.gcd(m, k) != 1 and False: pass
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            o = order_mod(r, m)
            if o != k: continue          # faithful action: ord(r) = k
            g = math.gcd(r - 1, m)
            if g > 2: continue
            if k % 2 == 0: phi = 'j'
            elif m % 2 == 0: phi = 'a'
            else: continue                # no index-2 subgroup via this quotient
            out.append((N, m, k, r, g, phi))
out.sort()
seen = set()
for row in out:
    print(*row)
print(len(out))

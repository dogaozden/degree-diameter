import math, sys
lo, hi = 406, 460
def order_mod(r, m):
    if math.gcd(r, m) != 1: return 0
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > m: return 0
    return o
out = []
for N in range(lo, hi + 1):
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            if order_mod(r, m) == 0: continue
            sub = frozenset(pow(r, t, m) for t in range(k))
            if sub in seen: continue
            seen.add(sub)
            out.append((N, m, k, r))
print(len(out))
with open("/home/user/degree-diameter/research/squads/raise10/r1/c08/meta_list.txt", "w") as f:
    for t in out: f.write("%d %d %d %d\n" % t)

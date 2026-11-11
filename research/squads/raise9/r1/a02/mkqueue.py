import math, sys
lo, hi = 254, 330
def order_mod(r, m):
    if math.gcd(r, m) != 1: return 0
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > m: return 0
    return o
out = []
for N in range(lo, hi + 1):
    out.append(f"cyc {N}")
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        seen = set()
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            key = min(pow(r, j, m) for j in range(1, k + 1) if math.gcd(j, k) == 1) if m > 1 else 1
            if key in seen: continue
            seen.add(key)
            out.append(f"meta {m} {k} {key}")
    # note: r=1 gives abelian Z_m x Z_k (included)
print(len(out), file=sys.stderr)
open("queue.txt", "w").write("\n".join(out) + "\n")

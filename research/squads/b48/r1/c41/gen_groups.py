# c41: list candidate groups of order N with an index-2 hom: cyc N, dih N/2, metacyclic Z_m x|_r Z_k (k even, ord(r) >= 3)
import sys, math
N = int(sys.argv[1]); out = []
out.append(f"cyc {N}")
if N % 2 == 0: out.append(f"dih {N//2}")
for k in range(2, N + 1, 2):
    if N % k: continue
    m = N // k
    if m < 3: continue
    ords = {}
    for r in range(2, m):
        if math.gcd(r, m) != 1: continue
        if pow(r, k, m) != 1 % m: continue
        o = 1; x = r
        while x != 1: x = x * r % m; o += 1
        if o >= 3 and math.gcd(r - 1, m) <= 2: ords.setdefault(o, r)
    for o, r in sorted(ords.items()):
        out.append(f"meta {m} {k} {r}")
print("\n".join(out))

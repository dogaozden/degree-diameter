import math, sys
def order_mod(r, m):
    if math.gcd(r, m) != 1: return 0
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > m: return 0
    return o
def groups(lo, hi):
    """(N, m, k, r): Z_m x|_r Z_k, r of order exactly k mod m, one r per cyclic subgroup <r> of order k."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N + 1):
            if N % k: continue
            m = N // k
            if m < 3: continue
            seen = set(); 
            for r in range(2, m):
                if order_mod(r, m) != k: continue
                sub = frozenset(pow(r, t, m) for t in range(k))
                if sub in seen: continue
                seen.add(sub)
                out.append((N, m, k, r))
    return out
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    g = groups(lo, hi)
    print(len(g), "groups in", lo, hi)
    from collections import Counter
    c = Counter((N // 100) * 100 for N, _, _, _ in g)
    print(sorted(c.items()))

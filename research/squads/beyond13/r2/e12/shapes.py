#!/usr/bin/env python3
"""List odd-order shapes near target group orders: meta(m,k,r) x Z_n and meta x meta (x Z_n). Prints spec args."""
import sys, math
def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0: return False
        i += 2
    return True
def metas(lo, hi, kset=None):
    """(m,k,r) with m prime, k odd prime dividing m-1, r of exact order k mod m, m*k in [lo,hi]."""
    out = []
    for k in ([kset] if kset else [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]):
        for m in range(max(3, lo // k), hi // k + 2):
            if m % 2 == 0 or not isprime(m) or (m - 1) % k: continue
            if not (lo <= m * k <= hi): continue
            r = None
            for x in range(2, m):
                t = pow(x, (m - 1) // k, m)
                if t != 1: r = t; break
            if r is None: continue
            out.append((m, k, r))
    return out
if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "meta":            # meta lo hi n   -> meta x Z_n
        lo, hi, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        for m, k, r in metas(lo // n, hi // n):
            print(f"meta {m} {k} {r} n {n} N={m*k*n}")
    elif mode == "prod":          # prod lo hi n  -> meta x meta x Z_n with m1k1*m2k2*n in range (k_i >= 5)
        lo, hi, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        A = [x for x in metas(lo // n // 1500, hi // n // 500 + 1) if x[0]*x[1] < hi // n]
        print(len(A), file=sys.stderr)

# Enumerate metacyclic groups Z_m x|_r Z_k (m composite, ord_m(r)=k, faithful), grouped by cyclic subgroup <r> of Z_m^*.
import math, sys

def ordmod(r, m):
    x, k = r % m, 1
    while x != 1 % m:
        x = (x * r) % m
        k += 1
    return k

def is_prime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))

def cands(lo, hi, abmax=40):
    out = []
    for m in range(4, hi + 1):
        if is_prime(m):
            continue
        for k in range(2, hi // m + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            seen = set()
            for r in range(2, m):
                if math.gcd(r, m) != 1 or ordmod(r, m) != k:
                    continue
                H = frozenset(pow(r, j, m) for j in range(k))
                if H in seen:
                    continue
                seen.add(H)
                # abelianization order = k * gcd(m, r-1); verify invariant over generators
                ab = {k * math.gcd(m, (pow(r, j, m) - 1) % m if (pow(r, j, m) - 1) % m else m) for j in range(1, k) if math.gcd(j, k) == 1}
                g = k * math.gcd(m, r - 1)
                if g <= abmax:
                    out.append((N, m, k, r, g, sorted(ab)))
    return out

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for c in sorted(cands(lo, hi), key=lambda t: (t[4], t[0])):
        N, m, k, r, g, ab = c
        print(f"N={N} m={m} k={k} r={r} abel={g} abel_all={ab}")

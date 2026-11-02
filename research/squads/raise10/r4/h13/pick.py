import sys, random
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
def gen(p):
    fs = []; m = p - 1; d = 2
    while d * d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs): return g
def frob_list(lo, hi, kmin=3, kmax=None):
    """(N=pk, p, k, r) for meta p k r with pk in [lo,hi], r of order exactly k mod p."""
    out = []
    kmax = hi if kmax is None else min(kmax, hi)
    for k in range(kmin, kmax + 1):
        for p in range(max(2, lo // k), hi // k + 1):
            if (p - 1) % k or p * k < lo or p * k > hi or not isprime(p): continue
            r = pow(gen(p), (p - 1) // k, p)
            out.append((p * k, p, k, r))
    return out
if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "single":
        L = frob_list(4021921, 4080000, 31, 127)
        random.seed(1); random.shuffle(L)
        for x in L[:10]: print("single", x)
    elif mode == "a4":
        L = frob_list(335161, 340000, 3)
        random.seed(2); random.shuffle(L)
        for x in L[:6]: print("a4", x, 12 * x[0])
    elif mode == "z21":
        L = frob_list(191521, 194285, 3)
        random.seed(3); random.shuffle(L)
        for x in L[:6]: print("z21", x, 21 * x[0])
    elif mode == "ff":
        L = frob_list(1000, 4100, 3)
        pairs = [(a, b) for a in L for b in L if a[0] <= b[0] and 4021921 <= a[0] * b[0] <= 4080000 and a[2] != b[2]]
        random.seed(4); random.shuffle(pairs)
        for a, b in pairs[:8]: print("ff", a, b, a[0] * b[0])

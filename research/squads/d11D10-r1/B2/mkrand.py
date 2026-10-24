"""Random Haar-graph solution files over SL/PSL(2,q) x Z_n (B2 test generator; same format as haar_sym writes).
Usage: mkrand.py OUT.txt sl|psl p e POLY_or_- n D SEED   (POLY e.g. x^2+1, '-' when e = 1)"""
import random, sys

def main():
    out, grp, p, e, poly_s, n, D, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], int(sys.argv[6]), int(sys.argv[7]), int(sys.argv[8])
    q = p ** e
    rng = random.Random(seed)
    if e == 1:
        poly = [0, 1]
        poly_s = None
    else:
        coeffs = {}
        for term in poly_s.split("+"):
            import re
            m = re.fullmatch(r"(\d*)(x(\^(\d+))?)?", term)
            c = int(m.group(1)) if m.group(1) else 1
            ex = (int(m.group(4)) if m.group(4) else 1) if m.group(2) else 0
            coeffs[ex] = (coeffs.get(ex, 0) + c) % p
        poly = [coeffs.get(i, 0) for i in range(e + 1)]
        assert poly[e] == 1
    dig = lambda x: [(x // p ** i) % p for i in range(e)]
    enc = lambda ds: sum(c * p ** i for i, c in enumerate(ds))
    def add(a, b):
        return enc([(x + y) % p for x, y in zip(dig(a), dig(b))])
    def mul(a, b):
        pr = [0] * (2 * e)
        for i, x in enumerate(dig(a)):
            for j, y in enumerate(dig(b)):
                pr[i + j] = (pr[i + j] + x * y) % p
        for i in range(2 * e - 2, e - 1, -1):
            t = pr[i]
            if t:
                for j in range(e + 1):
                    pr[i - e + j] = (pr[i - e + j] - t * poly[j]) % p
        return enc(pr[:e])
    neg = [next(b for b in range(q) if add(a, b) == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul(a, b) == 1)
    psl_odd = grp == "psl" and q % 2 == 1
    G0 = q * (q * q - 1) // (2 if psl_odd else 1)
    N = G0 * n
    def canon(a, b, c, d):
        if not psl_odd:
            return (a, b, c, d)
        lead = a if a else b
        pos = lead < neg[lead]
        if pos:
            return (a, b, c, d)
        return (neg[a], neg[b], neg[c], neg[d])
    import os
    borel = os.environ.get("BOREL") == "1"   # upper-triangular generators only: <S> lies in a Borel subgroup
    def rand_sl():
        while True:
            a, b, c = rng.randrange(q), rng.randrange(q), rng.randrange(q)
            if borel:
                if not a:
                    continue
                return a, b, 0, inv[a]
            if a:
                d = mul(add(1, mul(b, c)), inv[a])
            else:
                if not b or c != neg[inv[b]]:
                    continue
                d = rng.randrange(q)
            if add(mul(a, d), neg[mul(b, c)]) == 1:
                return a, b, c, d
    S, keys = [], set()
    while len(S) < 11:
        a, b, c, d = rand_sl()
        z = rng.randrange(n)
        k = (canon(a, b, c, d), z)
        if k in keys:
            continue
        keys.add(k)
        S.append((a, b, c, d, z))
    gname = f"{grp} {q}" + (f" poly {poly_s}" if poly_s else "")
    with open(out, "w") as f:
        f.write(f"11 {D} {gname} n {n} N {N}\n")
        for i, (a, b, c, d, z) in enumerate(S):
            # randomly negate matrices in PSL to test canonicalisation
            if psl_odd and rng.random() < 0.5:
                a, b, c, d = neg[a], neg[b], neg[c], neg[d]
            f.write(f"{i} mat({a},{b},{c},{d}) z={z}\n")
    print("wrote", out, "N=", N, "vertices=", 2 * N)

main()

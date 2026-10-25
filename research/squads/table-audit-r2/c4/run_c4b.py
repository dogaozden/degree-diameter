#!/usr/bin/env python3
"""card c4, second batch: Z_5^2 x| (Z_K1 x Z_K2) with commuting A, B in GL(2,5), K1*K2 = 16 (order 400)."""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run_c4 as R
from run_c4 import mm2, mpow, I2, G

def key(A):
    a, b, c, d = A
    return ((a + d) % 5, (a * d - b * c) % 5, b == 0 and c == 0 and a == d)

def z2sd2(p, K1, K2, A, B):
    Pw = [I2]
    for _ in range(K1 - 1): Pw.append(mm2(Pw[-1], A, p))
    Qw = [I2]
    for _ in range(K2 - 1): Qw.append(mm2(Qw[-1], B, p))
    def mul(g, h):
        (x, y, i, j), (u, v, k, l) = g, h
        M = mm2(Pw[i], Qw[j], p)
        return ((x + M[0] * u + M[1] * v) % p, (y + M[2] * u + M[3] * v) % p, (i + k) % K1, (j + l) % K2)
    els = [(x, y, i, j) for x in range(p) for y in range(p) for i in range(K1) for j in range(K2)]
    return G.from_mul(els, mul, (0, 0, 0, 0))

def pairs(K1, K2):
    mats = [A for A in itertools.product(range(5), repeat=4) if (A[0]*A[3]-A[1]*A[2]) % 5]
    Ak = [A for A in mats if mpow(A, K1, 5) == I2]
    Bk = [B for B in mats if mpow(B, K2, 5) == I2]
    seen, out = set(), []
    for A in Ak:
        for B in Bk:
            if A == I2 and B == I2: continue
            if mm2(A, B, 5) != mm2(B, A, 5): continue
            k = (key(A), key(B), key(mm2(A, B, 5)))
            if k in seen: continue
            seen.add(k); out.append((A, B))
    return out

if __name__ == "__main__":
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    specs = []
    for K1, K2 in [(4, 4), (8, 2), (2, 8)]:
        ps = pairs(K1, K2)
        print(K1, K2, len(ps), flush=True)
        for A, B in ps:
            lab = f"z2sd2_5_{K1}_{K2}_{''.join(map(str, A))}_{''.join(map(str, B))}"
            specs.append((lab, lambda K1=K1, K2=K2, A=A, B=B: z2sd2(5, K1, K2, A, B)))
    # keep a deterministic spread of the list up to cap
    step = max(1, len(specs) // cap)
    specs = specs[::step][:cap]
    print("running", len(specs), flush=True)
    res = []
    for lab, build in specs:
        try:
            best, zero = R.run(lab, build, None)
            res.append((best, lab, zero))
            if zero: print("FOUND", lab, flush=True)
        except Exception as e:
            print("ERROR", lab, e, flush=True)
    res.sort()
    print("TOP", res[:5], flush=True)

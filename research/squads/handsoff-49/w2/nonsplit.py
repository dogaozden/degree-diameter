"""Non-split metacyclic groups G = <a,b | a^m=1, b^k=a^s, b a b^-1 = a^r>, order m*k, k >= 3, s != 0, s(r-1) = 0 mod m.
Element a^i b^j has index j*m + i (identity 0).  Usage: nonsplit.py LO HI LIST  (writes "N m k r s" lines) or
nonsplit.py --table m k r s OUT.bin  (writes the int32 N + uint16 N*N table for haar_tab's 'tab' group)."""
import sys, math
import numpy as np

def params(m, k, r):
    R = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    return R

def table(m, k, r, s):
    N = m * k
    R = params(m, k, r)
    x = np.arange(N, dtype=np.int64)
    I, J = (x % m)[:, None], (x // m)[:, None]
    P, Q = (x % m)[None, :], (x // m)[None, :]
    tot = J + Q
    wrap = tot >= k
    nj = tot - k * wrap
    ni = (I + R[J] * P + s * wrap) % m
    return (nj * m + ni).astype(np.uint16)

def write_bin(T, path):
    with open(path, "wb") as f:
        np.array([T.shape[0]], dtype=np.int32).tofile(f)
        np.ascontiguousarray(T, dtype=np.uint16).tofile(f)

if __name__ == "__main__":
    if sys.argv[1] == "--table":
        m, k, r, s = map(int, sys.argv[2:6]); write_bin(table(m, k, r, s), sys.argv[6]); sys.exit()
    LO, HI = int(sys.argv[1]), int(sys.argv[2])
    out = []
    for N in range(LO, HI + 1):
        for m in range(3, N + 1):
            if N % m: continue
            k = N // m
            if k < 3: continue
            units_seen = set()
            for r in range(2, m):
                if math.gcd(r, m) != 1: continue
                if pow(r, k, m) != 1 % m: continue
                sub = frozenset(pow(r, t, m) for t in range(k))  # subgroup generated (order divides k)
                if sub in units_seen: continue
                units_seen.add(sub)
                g = math.gcd(r - 1, m)
                if g == 1: continue          # s(r-1)=0 forces s=0: only split
                for s in range(m):
                    if s == 0 or (s * (r - 1)) % m: continue
                    out.append((N, m, k, r, s))
    print(len(out), file=sys.stderr)
    with open(sys.argv[3], "w") as f:
        for t in out: f.write("%d %d %d %d %d\n" % t)

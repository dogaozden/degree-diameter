import sys, math
def groups(m):
    out = []
    for A in range(2, m + 1):
        if m % A: continue
        B = m // A
        for R in range(2, A):
            if math.gcd(R, A) != 1: continue
            if pow(R, B, A) != 1 % A: continue
            if R % A == 1: continue
            # keep one representative per (A,B,order of R)
            out.append((A, B, R))
    # dedupe by order of R mod A
    seen = {}
    res = []
    for A, B, R in out:
        o = 1; x = R % A
        while x != 1 % A: x = x * R % A; o += 1
        key = (A, B, o)
        if key in seen: continue
        seen[key] = 1
        res.append((A, B, R))
    return res
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for m in range(lo, hi + 1):
        for A, B, R in groups(m):
            print(m, A, B, R)

import math, sys
def metas(N):
    out = []
    for k in range(2, N+1, 2):
        if N % k: continue
        m = N // k
        seen = set()
        for r in range(1, max(m,2)):
            if m == 1:
                if r == 1: out.append((m,k,r))
                continue
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            out.append((m,k,r))
    return out
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for N in range(lo, hi+1):
        L = metas(N)
        if L: print(N, len(L), ' '.join(f"{m}:{k}:{r}" for m,k,r in L))

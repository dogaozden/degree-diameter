# Non-split metacyclic groups G = <a,x | a^m=1, x^k=a^t, x a x^-1 = a^r>, order m*k.
# Element index a + m*j (a in Z_m, j in [0,k)). Table written in groups.py .bin format (identity 0).
import sys, numpy as np
from math import gcd

def build(m, k, r, t):
    N = m * k
    rp = [pow(r, e, m) for e in range(k)]
    T = np.zeros((N, N), dtype=np.uint16)
    for j in range(k):
        for l in range(k):
            s = j + l
            if s < k:
                J, extra = s, 0
            else:
                J, extra = s - k, t
            for a in range(m):
                for b in range(m):
                    c = (a + rp[j] * b + extra * rp[J]) % m
                    T[a + m * j, b + m * l] = c + m * J
    return T

def check(T):
    N = len(T)
    assert T[0, 0] == 0 and (T[0] == np.arange(N)).all()
    rng = np.random.default_rng(1)
    for _ in range(3000):
        x, y, z = rng.integers(0, N, 3)
        assert T[T[x, y], z] == T[x, T[y, z]], "not associative"
    return True

def inv_and_orders(T):
    N = len(T)
    ident = 0
    orders = np.zeros(N, dtype=int)
    for g in range(N):
        p, o = g, 1
        while p != ident:
            p = T[p, g]; o += 1
        orders[g] = o
    return orders

def is_split(T, m, k):
    # split iff some coset element a^c x has order k
    orders = inv_and_orders(T)
    for c in range(m):
        if orders[c + m * 1] == k:
            return True
    return False

def write_bin(T, path):
    with open(path, 'wb') as f:
        np.array([len(T)], dtype=np.int32).tofile(f)
        np.ascontiguousarray(T, dtype=np.uint16).tofile(f)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'list':
        LO, HI = int(sys.argv[2]), int(sys.argv[3])
        out = []
        for N in range(LO, HI + 1):
            for k in range(2, N + 1):
                if N % k: continue
                m = N // k
                if m < 2: continue
                for r in range(2, m):
                    if gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
                    if (r - 1) % m == 0: continue
                    for t in range(1, m):
                        if (t * (r - 1)) % m != 0: continue
                        out.append((m, k, r, t))
        print(len(out))
        for o in out: print(*o)
    elif mode == 'build':
        m, k, r, t, path = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        T = build(m, k, r, t)
        check(T)
        write_bin(T, path)
        o = inv_and_orders(T)
        print("N", len(T), "split", is_split(T, m, k), "involutions", int((o == 2).sum()), "maxorder", int(o.max()))

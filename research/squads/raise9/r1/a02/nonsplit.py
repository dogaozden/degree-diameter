import math, sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import groups
def table_ns(m, k, r, s):
    N = m * k
    el = [(x, y) for y in range(k) for x in range(m)]   # index x + m*y
    rp = [pow(r, t, m) for t in range(k)]
    T = np.empty((N, N), dtype=np.uint16)
    for i, (x, y) in enumerate(el):
        for j, (u, v) in enumerate(el):
            w = y + v
            if w >= k:
                a = (x + rp[y] * u + s * rp[w - k]) % m
                w -= k
            else:
                a = (x + rp[y] * u) % m
            T[i, j] = a + m * w
    return T
def ok(T):
    N = len(T)
    if not (T[0] == np.arange(N)).all() or not (T[:, 0] == np.arange(N)).all(): return False
    rng = np.random.default_rng(3)
    for _ in range(3000):
        g, h, q = rng.integers(0, N, 3)
        if T[T[g, h], q] != T[g, T[h, q]]: return False
    return all(len(set(T[g].tolist())) == N for g in range(N))
if __name__ == '__main__':
    specs = []
    cnt_bad = 0
    for N in range(254, 331):
        for k in range(2, N + 1):
            if N % k: continue
            m = N // k
            if m < 2: continue
            for r in range(1, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
                for s in range(1, m):
                    if (s * (r - 1)) % m: continue
                    specs.append((N, m, k, r, s))
    print(len(specs), file=sys.stderr)
    import pickle
    pickle.dump(specs, open('nonsplit_specs.pkl', 'wb'))

# c8: find isometries of V of order divisible by 37 (Singer-like, q^3+1 = 1332 = 4*9*37), orbits on E, orbit clique.
import sys, time, math
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O

I6 = np.eye(6, dtype=np.int64)

def order_of(g, cap=400000):
    h = g.copy()
    for k in range(1, cap + 1):
        if np.array_equal(h, I6): return k
        h = (h @ g) % 11
    return None

def mpow(g, e):
    r = I6.copy(); b = g.copy()
    while e:
        if e & 1: r = (r @ b) % 11
        b = (b @ b) % 11; e >>= 1
    return r

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    ntry = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    rng = np.random.default_rng(seed)
    hits = []
    stats = {}
    t0 = time.time()
    for t in range(ntry):
        k = int(rng.integers(3, 11))
        g = O.rand_elem(rng, k)
        o = order_of(g)
        stats[o] = stats.get(o, 0) + 1
        if o is not None and o % 37 == 0:
            h = mpow(g, o // 37)
            assert np.array_equal(h.T @ O.M @ h % 11, O.M % 11)
            hits.append(h)
            if len(hits) >= 3: break
    print("tried", t + 1, "time", round(time.time() - t0, 1), "hits", len(hits))
    print("order histogram (top):", sorted(stats.items(), key=lambda x: -x[1])[:25])
    if hits:
        np.save(f'/home/user/degree-diameter/research/squads/d14D7-r4/c8/g37_s{seed}.npy', hits[0])
        print("g37 matrix:\n", hits[0])

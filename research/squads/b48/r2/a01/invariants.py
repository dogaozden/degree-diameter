import sys, glob, numpy as np
from collections import Counter
def load(path):
    with open(path, "rb") as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64)
    return N, T
def invariants(N, T):
    # identity: the element e with T[e,x]=x for all x
    e = [i for i in range(N) if (T[i] == np.arange(N)).all()][0]
    assert e == 0
    orders = np.zeros(N, dtype=int)
    for g in range(N):
        x, k = g, 1
        while x != e:
            x = T[x, g]; k += 1
        orders[g] = k
    cnt = tuple(sorted(Counter(orders.tolist()).items()))
    # centre size
    Z = sum(1 for g in range(N) if all(T[g, h] == T[h, g] for h in range(N)))
    # associativity spot check
    rng = np.random.default_rng(1)
    ok = all(T[T[a, b], c] == T[a, T[b, c]] for a, b, c in rng.integers(0, N, (2000, 3)))
    return cnt, Z, ok
for p in sys.argv[1:]:
    N, T = load(p)
    cnt, Z, ok = invariants(N, T)
    print(p.split('/')[-1], "centre", Z, "assoc_ok", ok, "orders", cnt)

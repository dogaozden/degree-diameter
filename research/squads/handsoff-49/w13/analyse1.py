import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
m, k, r = map(int, sys.argv[1:4])
T = meta_table(m, k, r); Sinv = inverses(T)
N = T.shape[0]
print("N", N, "inv ok", np.all(T[np.arange(N), Sinv] == 0))
rng = np.random.default_rng(1)
best = None
t0 = time.time(); cnt = 0
for it in range(int(sys.argv[4])):
    S = [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
    f = far_set(T, S, Sinv)
    cnt += 1
    if best is None or len(f) < best[0]:
        best = (len(f), S, f)
        print(it, "missing", len(f), "S", S, "elems", [(int(x % m), int(x // m)) for x in f][:10], flush=True)
print("evals", cnt, "time", round(time.time()-t0, 2))

import sys, numpy as np, random
f = sys.argv[1]
with open(f, "rb") as h:
    N = int(np.fromfile(h, dtype=np.int32, count=1)[0])
    T = np.fromfile(h, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64)
assert (T[0] == np.arange(N)).all() and (T[:, 0] == np.arange(N)).all(), "identity"
ok = True
rng = np.random.default_rng(1)
for _ in range(3000):
    a, b, c = rng.integers(0, N, 3)
    if T[T[a, b], c] != T[a, T[b, c]]:
        ok = False; break
inv = all((T[np.arange(N), :] == 0).sum(axis=1) == 1)
print(f, N, "assoc_ok" if ok else "ASSOC_FAIL", "latin" if inv else "")

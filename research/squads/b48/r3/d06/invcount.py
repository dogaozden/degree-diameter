# count involutions and check table size for a list of .bin tables (args: files)
import sys
import numpy as np
for fn in sys.argv[1:]:
    with open(fn, "rb") as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)
    # involution: g != e and g*g == e ; identity index 0
    sq = T[np.arange(N), np.arange(N)]
    inv = int(np.sum((sq == 0))) - 1
    print(fn.split("/")[-1], N, "involutions", inv)

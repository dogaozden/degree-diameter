# edge list of H(G,S) from a groups.py table: (g,A) ~ (s g, B); A = 0..N-1, B = N..2N-1
import sys
import numpy as np
tab, out, S = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(",")]
with open(tab, "rb") as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)
with open(out, "w") as f:
    f.write(f"{2 * N}\n")
    for s in S:
        for g in range(N):
            f.write(f"{g} {N + int(T[s, g])}\n")
print(out, 2 * N)

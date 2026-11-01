"""Edge list of a haar_tab solution (Haar graph, edges (g,A) ~ (s g, B), A = 0..N-1, B = N..2N-1).
Usage: python3 haar_tab_edges.py SOL.txt [TABLE.bin] OUT.edges   (the table path is read from the header if omitted)"""
import sys
import numpy as np
sol = sys.argv[1]
lines = open(sol).read().split("\n")
hdr = lines[0].split()
tab = sys.argv[2] if len(sys.argv) > 3 else hdr[hdr.index("tab") + 1]
out = sys.argv[-1]
with open(tab, "rb") as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)
assert int(hdr[hdr.index("n") + 1]) == 1, "only Z_1 supported"
S = [int(l.split()[0]) for l in lines[1:] if l.strip() and not l.startswith("#")]
with open(out, "w") as f:
    f.write(f"{2 * N}\n")
    for s in S:
        for g in range(N):
            f.write(f"{g} {N + int(T[s, g])}\n")
print(out, 2 * N, len(S) * N, "S =", S)

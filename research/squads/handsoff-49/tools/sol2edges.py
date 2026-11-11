"""Edge list of a haar_tab solution file whose group is "meta m k r" or "tab FILE.bin" (with n = 1).
Haar graph H(G,S): vertices (g,A) = g, (g,B) = N + g; edges (g,A) ~ (s g, B).  (handsoff-49 job)
Usage: python3 sol2edges.py SOL OUT.edges"""
import sys, re
sys.path.insert(0, __import__("os").path.dirname(__file__))
import numpy as np
sol, out = sys.argv[1], sys.argv[2]
lines = open(sol).read().split("\n")
hdr = lines[0].split()
assert int(hdr[hdr.index("n") + 1]) == 1, "only Z_1 supported"
if hdr[2] == "meta":
    m, k, r = int(hdr[3]), int(hdr[4]), int(hdr[5])
    N = m * k
    S = []
    for l in lines[1:]:
        mm = re.search(r"meta\(a=(\d+),j=(\d+)\)", l)
        if mm: S.append((int(mm.group(1)), int(mm.group(2))))
    def mul(x, y):  # (a,j)(b,l) = (a + r^j b, j + l)
        return ((x[0] + pow(r, x[1], m) * y[0]) % m, (x[1] + y[1]) % k)
    with open(out, "w") as f:
        f.write(f"{2 * N}\n")
        for s in S:
            for a in range(m):
                for j in range(k):
                    g = (a, j); h = mul(s, g)
                    f.write(f"{a + m * j} {N + h[0] + m * h[1]}\n")
    print(out, 2 * N, len(S) * N, "S =", S)
else:
    tab = hdr[hdr.index("tab") + 1]
    with open(tab, "rb") as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)
    S = [int(l.split()[0]) for l in lines[1:] if l.strip() and not l.startswith("#")]
    with open(out, "w") as f:
        f.write(f"{2 * N}\n")
        for s in S:
            for g in range(N):
                f.write(f"{g} {N + int(T[s, g])}\n")
    print(out, 2 * N, len(S) * N, "S =", S)

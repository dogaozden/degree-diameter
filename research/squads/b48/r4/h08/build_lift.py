# Build the lift edge list of b22_cubic over meta:m:k:r (flift convention: left multiplication, index a + m*j).
# usage: build_lift.py m k r v0 v1 v2 v3 v4 v5 OUT.edges
import sys
m, k, r = map(int, sys.argv[1:4]); volts = list(map(int, sys.argv[4:10])); out = sys.argv[10]
N = m * k
def mul(x, y):
    a, j = x % m, x // m; b, l = y % m, y // m
    return ((a + pow(r, j, m) * b) % m) + m * ((j + l) % k)
base = [(0, 2), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)]
E = []
for (u, v), g in zip(base, volts):
    for x in range(N):
        E.append((u * N + x, v * N + mul(g, x)))
with open(out, "w") as f:
    f.write(f"{4 * N}\n")
    for a, b in E:
        f.write(f"{a} {b}\n")
print("edges", len(E), "n", 4 * N)

# build the lift edge list for meta:55:20:2 dipole4 with voltages (0, x, y, z), x=(a,j) index a+55j; vertex (v,x)=v*N+x
import sys
M, K, R = 55, 20, 2
N = M * K
def mul(g, h):
    a, j = g % M, g // M
    b, l = h % M, h // M
    return ((a + pow(R, j, M) * b) % M) + M * ((j + l) % K)
volts = [int(v) for v in sys.argv[1].split(",")]
out = sys.argv[2]
edges = []
for g in volts:
    for x in range(N):
        edges.append((x, N + mul(x, g)))
with open(out, "w") as f:
    f.write(f"{2*N}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
print("wrote", out, len(edges))

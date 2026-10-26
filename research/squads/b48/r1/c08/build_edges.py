# Build the Haar graph H(G, S) edge list (side A = 0..N-1, side B = N..2N-1; (A,x) ~ (B, x*s) for s in S)
# for G = meta m k r, index a + m*j, (a,j)(b,l) = (a + r^j b, j + l). Output: "n" then "u v" lines.
import sys
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
S = [int(x) for x in sys.argv[4].split(",")]
out = sys.argv[5]
N = m * k
def mul(x, y):
    a, j = x % m, x // m
    b, l = y % m, y // m
    return (a + pow(r, j, m) * b) % m + m * ((j + l) % k)
E = []
for s in S:
    for x in range(N):
        E.append((x, N + mul(x, s)))
with open(out, "w") as f:
    f.write(f"{2*N}\n")
    for u, v in E: f.write(f"{u} {v}\n")
print("edges", len(E), "n", 2*N)

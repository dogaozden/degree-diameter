# build the lift edge list for meta m k r with base edges: e1 (0-1, identity), e2 (0-1, g2), s0 (semi at 0), s1 (semi at 1)
import sys
m, k, r, g2, s0, s1 = map(int, sys.argv[1:7]); out = sys.argv[7]
N = m * k
def mul(x, g):
    a, j = x % m, x // m
    c, l = g % m, g // m
    return ((a + pow(r, j, m) * c) % m) + m * ((j + l) % k)
E = set()
for x in range(N):
    E.add((0 * N + x, 1 * N + x))
    E.add((0 * N + x, 1 * N + mul(x, g2)))
for x in range(N):
    y = mul(x, s0); E.add(tuple(sorted((0 * N + x, 0 * N + y))))
    y = mul(x, s1); E.add(tuple(sorted((1 * N + x, 1 * N + y))))
with open(out, "w") as f:
    f.write(f"{2 * N}\n")
    for u, v in sorted(E): f.write(f"{u} {v}\n")
print("edges", len(E))

# build the lift edge list for base 2 3 / 0 1 / 0 0 / 1 1 (edge voltage e, loops g0, g1) over meta m k r
import sys
m, k, r, g0, g1 = map(int, sys.argv[1:6]); out = sys.argv[6]
N = m * k
def mul(x, g):
    a, j = x % m, x // m
    b, l = g % m, g // m
    return (a + pow(r, j, m) * b) % m + m * ((j + l) % k)
E = set()
for x in range(N):
    E.add((x, N + x))                              # matching edge (0,x)-(1,x)
    for g, base in ((g0, 0), (g1, N)):
        y = mul(x, g)
        E.add(tuple(sorted((base + x, base + y))))
with open(out, 'w') as f:
    f.write(f"{2*N}\n")
    for u, v in sorted(E): f.write(f"{u} {v}\n")
print(len(E), "edges")

"""genbase.py A SEED OUT: random connected cubic bipartite multigraph on A+A vertices (perfect-matching model)."""
import sys, random
a, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
r = random.Random(seed)
while True:
    E = []
    for _ in range(3):
        p = list(range(a)); r.shuffle(p)
        E += [(i, a + p[i]) for i in range(a)]
    par = list(range(2 * a))
    def f(x):
        while par[x] != x: x = par[x]
        return x
    for u, v in E: par[f(u)] = f(v)
    if len({f(x) for x in range(2 * a)}) == 1: break
with open(out, "w") as o:
    o.write(f"{2*a} {len(E)}\n" + "\n".join(f"{u} {v}" for u, v in E) + "\n")

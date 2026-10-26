"""randvolt.py BASEFILE K SEED: K random voltage lines for a base (b m, m edges). Spanning-tree edges get 0,
the others uniform in Z_N (N read from env GN). Gauge-equivalent to all voltages random."""
import sys, random, os
bf, K, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
N = int(os.environ["GN"])
lines = open(bf).read().split("\n")
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split())) for i in range(m)]
par = list(range(b))
def f(x):
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x
tree = [False] * m
for i, (u, v) in enumerate(E):
    if f(u) != f(v):
        par[f(u)] = f(v); tree[i] = True
free = [i for i in range(m) if not tree[i]]
r = random.Random(seed)
for _ in range(K):
    v = [0] * m
    for i in free:
        v[i] = r.randrange(1, N) if os.environ.get("NOID") else r.randrange(N)
    print(" ".join(map(str, v)))

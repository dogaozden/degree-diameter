# Random (timing-only) instance in the solution-file format: gen_synth.py p n d seed D OUT
import random, sys
p, n, d, seed, D = map(int, sys.argv[1:6])
out = sys.argv[6]
rng = random.Random(seed)
N = n * p * (p * p - 1) // 2
def cls(m):
    neg = tuple((-x) % p for x in m)
    return min(tuple(m), neg)
seen, gens = set(), []
while len(gens) < d:
    a = rng.randrange(1, p); b = rng.randrange(p); c = rng.randrange(p)
    dd = (1 + b * c) * pow(a, p - 2, p) % p
    m = (a, b, c, dd)
    z = rng.randrange(n)
    key = (cls(m), z)
    if key in seen:
        continue
    seen.add(key); gens.append((m, z))
with open(out, "w") as f:
    f.write("%d %d psl %d n %d N %d\n" % (d, D, p, n, N))
    for i, (m, z) in enumerate(gens):
        f.write("%d mat(%d,%d,%d,%d) z=%d\n" % (i, m[0], m[1], m[2], m[3], z))
print("wrote", out, "N=", N)

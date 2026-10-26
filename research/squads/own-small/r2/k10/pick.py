# pick.py GT64 NPICK: list groups of order 64 with their minimal-generator estimate d (random tries),
# sample NPICK groups preferring d=2 (then d=3), print "id d name" lines in the chosen order.
import sys, random
path, npick = sys.argv[1], int(sys.argv[2])
groups = []
cur = None
for line in open(path):
    s = line.split()
    if not s: continue
    if s[0] == 'G':
        cur = {'N': int(s[1]), 'id': int(s[2]), 'name': ' '.join(s[3:]), 'vals': []}
        groups.append(cur)
    else:
        cur['vals'] += [int(x) for x in s]
rng = random.Random(7)
def closure(N, mul, gens):
    seen = {0}; frontier = [0]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = mul[x * N + g]
                if y not in seen:
                    seen.add(y); nf.append(y)
        frontier = nf
    # closure under right mult by gens already gives the generated subgroup for finite groups
    return len(seen)
res = []
for g in groups:
    N = g['N']; mul = g['vals']
    assert len(mul) == N * N, (g['id'], len(mul))
    d = None
    for k in range(1, 9):
        ok = False
        for _ in range(40):
            gens = [rng.randrange(N) for _ in range(k)]
            if closure(N, mul, gens) == N:
                ok = True; break
        if ok:
            d = k; break
    res.append((d, g['id'], g['name']))
from collections import Counter
print('# d histogram', sorted(Counter(str(r[0]) for r in res).items()), file=sys.stderr)
pool2 = [r for r in res if r[0] == 2]
pool3 = [r for r in res if r[0] == 3]
rng.shuffle(pool2); rng.shuffle(pool3)
chosen = (pool2 + pool3 + [r for r in res if r[0] not in (2, 3)])[:npick]
for d, gid, name in chosen:
    print(gid, d, name)

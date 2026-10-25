# c6: injective rainbow start: colour -> distinct nonzero voltage in Z_m (no level skeleton); writes a base file
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import rainbow, gq
q, m, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
G = gq.load(q); N = G['N']
rnd = random.Random(4242 + seed * 31 + m)
mats = rainbow.factorize(q, seed)
Mp = []
for t in range(2):
    perm = list(range(N)); rnd.shuffle(perm); Mp.append(perm)
cm = list(mats) + Mp
volt = rnd.sample(range(1, m), q + 3)
edges = []
for c in range(q + 3):
    for p in range(N):
        edges.append((p, N + cm[c][p], volt[c], 1 if c <= q else 100 + (c - q - 1)))
gq.write_base(out, 2 * N, m, edges)
print('wrote', out, 'volt', volt, rainbow.evaluate(out, 6)[1])

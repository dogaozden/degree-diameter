# c6: rainbow in Z_m without levels: colour -> voltage injective into Z_m \ {0} (each vertex sees distinct shifts)
import sys, random, statistics
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import rainbow, gq
q = int(sys.argv[1]); ms = [int(x) for x in sys.argv[2].split(',')]; seeds = int(sys.argv[3]); mode = sys.argv[4]
fn = '/home/user/degree-diameter/research/squads/d16D8-r2/c6/exp3_tmp_%d.base' % q
G = gq.load(q); N = G['N']
mats_cache = {}
for m in ms:
    res = []
    for s in range(seeds):
        rnd = random.Random(777 + s * 31 + m)
        if s not in mats_cache:
            mats_cache[s] = rainbow.factorize(q, s)
        mats = mats_cache[s]
        Mp = []
        for t in range(2):
            perm = list(range(N)); rnd.shuffle(perm); Mp.append(perm)
        cm = list(mats) + Mp
        if mode == 'inj':
            volt = rnd.sample(range(1, m), q + 3)
        else:
            volt = [rnd.randrange(1, m) for _ in range(q + 3)]
        edges = []
        for c in range(q + 3):
            for p in range(N):
                edges.append((p, N + cm[c][p], volt[c], 1 if c <= q else 100 + (c - q - 1)))
        gq.write_base(fn, 2 * N, m, edges)
        res.append(rainbow.evaluate(fn, 6)[0])
    print('q', q, 'm', m, mode, 'uncovered mean %.0f min %d max %d' % (statistics.mean(res), min(res), max(res)), flush=True)

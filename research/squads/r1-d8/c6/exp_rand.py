import random, time, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import *
q = int(sys.argv[1]); Ms = [int(x) for x in sys.argv[2].split(',')]; seeds = int(sys.argv[3])
H = load(q); N = H.N
for M in Ms:
    res = []
    for sd in range(seeds):
        rng = random.Random(1000 + sd)
        t = [rng.randrange(M) for _ in range(N)]
        s = list(range(N)); rng.shuffle(s)
        path = f'/home/user/degree-diameter/research/squads/r1-d8/c6/rand_q{q}_M{M}_s{sd}.txt'
        write_base(path, H, M, t, s)
        t0 = time.time()
        unr, ecc, out = liftdiam(path)
        res.append((unr, ecc, round(time.time() - t0, 1)))
    print(f'q={q} M={M} random: (unreached, max_ecc, secs) = {res}', flush=True)

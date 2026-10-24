import random, time, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import *
from cover_sa import cover_labels
q = int(sys.argv[1]); Ms = [int(x) for x in sys.argv[2].split(',')]; iters = int(sys.argv[3])
H = load(q); N = H.N; X = collinear_lists(H)
for M in Ms:
    best, t = cover_labels(H, M, 1, iters, X=X)
    for sd in range(2):
        rng = random.Random(77 + sd)
        s = list(range(N)); rng.shuffle(s)
        path = f'/home/user/degree-diameter/research/squads/r1-d8/c6/cov_q{q}_M{M}_s{sd}.txt'
        write_base(path, H, M, t, s)
        t0 = time.time()
        unr, ecc, out = liftdiam(path)
        print(f'q={q} M={M} cover_missing={best} randS{sd}: unreached={unr} max_ecc={ecc} secs={time.time()-t0:.1f}', flush=True)

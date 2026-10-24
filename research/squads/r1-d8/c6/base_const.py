import random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import load, write_base, liftdiam
q = int(sys.argv[1]); M = int(sys.argv[2]); tc = int(sys.argv[3])
H = load(q); N = H.N
for sd in range(2):
    rng = random.Random(sd)
    s = list(range(N)); rng.shuffle(s)
    path = f'/home/user/degree-diameter/research/squads/r1-d8/c6/const_q{q}_M{M}_t{tc}_s{sd}.txt'
    write_base(path, H, M, [tc] * N, s)
    unr, ecc, out = liftdiam(path, 8, 1)
    print(f'q={q} M={M} constant hop voltage {tc}, random s seed {sd}: unreached={unr} max_ecc={ecc}', flush=True)

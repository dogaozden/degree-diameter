import sys, random, subprocess, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c4')
from mult import *
q = int(sys.argv[1]); d = int(sys.argv[2]); variant = sys.argv[3]; seeds = int(sys.argv[4])
N, LP, PL, coord = load(q)
W = mult_voltages(q, N, LP, coord, spec=0)
m = 5 * d
LIFTEVAL = '/home/user/degree-diameter/research/squads/cells/d10D8_work/liftevalw'
rng_np = np.random.default_rng(11)
lines = []
for s in range(seeds):
    rng = np.random.default_rng(100 + s)
    if variant.startswith('mult'):          # flags carry multiplicative value mod d, matchings level +1,+2
        Wd = W % d
    elif variant == 'rand':        # baseline: uniform random Z_d on flags
        Wd = rng.integers(0, d, size=W.shape)
    flags = []
    for L in range(N):
        for k, p in enumerate(LP[L]):
            flags.append((int(p), L, crt(0, int(Wd[L, k]), d)))
    matchings = []
    for t in (1, 2):
        perm = rng.permutation(N)
        if variant == 'mult_rmatch':
            matchings.append((perm, crt(t, int(rng.integers(0, d)), d)))
        else:
            matchings.append((perm, crt(t, 0, d)))
    fn = f'/home/user/degree-diameter/research/squads/r1_d8c/c4/runs/lift_q{q}_d{d}_{variant}_s{s}.txt'
    os.makedirs(os.path.dirname(fn), exist_ok=True)
    write_lift(fn, N, m, np.array(flags), matchings)
    env = dict(os.environ, OMP_NUM_THREADS='1')
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', LIFTEVAL, fn, '8', 'all'], capture_output=True, text=True, env=env)
    out = (r.stdout + r.stderr).strip().splitlines()
    print(f'q{q} d{d} m{m} {variant} seed{s}: exit {r.returncode}', out[-1] if out else '', flush=True)

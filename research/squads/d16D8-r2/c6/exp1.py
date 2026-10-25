import sys, random, statistics
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import rainbow, gq
q = int(sys.argv[1]); k = (q + 5) // 2; m = 5 * k
G = gq.load(q); N = G['N']
def make(seed, mode):
    rnd = random.Random(seed)
    mats = rainbow.factorize(q, seed)
    M = [list(range(N)), list(range(N))]
    for t in range(2):
        rnd.shuffle(M[t])
    colour_match = mats + M
    # build the per-colour voltages for each mode
    f = [z for z in range(1, k) for _ in range(2)]; rnd.shuffle(f)
    if mode == 'rainbow0':
        lv = [0] * (q + 1) + [1, 2]
    elif mode == 'rainbowrandlev':  # rainbow in Z_k, flags random Z_5 residue per colour
        lv = [rnd.randrange(5) for _ in range(q + 1)] + [1, 2]
    elif mode == 'randomZk':        # no rainbow: f uniform in Z_k, flags level 0
        f = [rnd.randrange(k) for _ in range(q + 3)]; lv = [0] * (q + 1) + [1, 2]
    elif mode == 'randomZm':        # uniform random in Z_m, per colour
        f = [rnd.randrange(m) for _ in range(q + 3)]; lv = None
    if lv is None:
        volt = f
    else:
        volt = [rainbow.crt(lv[c], f[c], k) for c in range(q + 3)]
    edges = []
    for c in range(q + 3):
        Mc = colour_match[c]
        for p in range(N):
            edges.append((p, N + Mc[p], volt[c], 1 if c <= q else 100 + (c - q - 1)))
    return 2 * N, edges
import os
for mode in sys.argv[2].split(','):
    uncs = []
    for s in range(int(sys.argv[3])):
        V, E = make(1000 + s, mode)
        fn = '/home/user/degree-diameter/research/squads/d16D8-r2/c6/exp_tmp.base'
        gq.write_base(fn, V, m, E)
        u, out, valid = rainbow.evaluate(fn, 6)
        uncs.append(u)
    print(mode, 'q', q, 'm', m, 'uncovered mean %.0f' % statistics.mean(uncs), 'min', min(uncs), 'max', max(uncs), flush=True)

# c6: rainbow designs with arbitrary k (balanced f), spec levels (flags 0, M1 1, M2 2), written as baselift base files.
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import rainbow, gq
HERE = '/home/user/degree-diameter/research/squads/d16D8-r2/c6'

def balanced_f(q, k, rnd):
    """q+3 colour values in Z_k \\ {0}, each value used floor or ceil of (q+3)/(k-1) times, random assignment."""
    n = q + 3; vals = []
    base = n // (k - 1); extra = n - base * (k - 1)
    for z in range(1, k):
        vals += [z] * base
    for z in rnd.sample(range(1, k), extra):
        vals.append(z)
    rnd.shuffle(vals)
    return vals

def design(q, k, seed, mats=None, f=None, random_f=False, Mperm=None):
    """returns (V, m, edges, f). mats: 1-factorization (cached per q, seed 0 unless given)."""
    G = gq.load(q); N = G['N']; rnd = random.Random(seed * 1000003 + k)
    m = 5 * k
    if mats is None:
        mats = rainbow.factorize(q, seed)
    if Mperm is None:
        Mperm = []
        for t in range(2):
            perm = list(range(N)); rnd.shuffle(perm); Mperm.append(perm)
    if f is None:
        if random_f:
            f = [rnd.randrange(k) for _ in range(q + 3)]
        else:
            f = balanced_f(q, k, rnd)
    lv = [0] * (q + 1) + [1, 2]
    volt = [rainbow.crt(lv[c], f[c], k) for c in range(q + 3)]
    cm = list(mats) + Mperm
    edges = []
    for c in range(q + 3):
        for p in range(N):
            edges.append((p, N + cm[c][p], volt[c], 1 if c <= q else 100 + (c - q - 1)))
    return 2 * N, m, edges, f

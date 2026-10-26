"""Simulated annealing for large line sets on Q(4,5).
mode 'spread': pairwise non-concurrent.
mode 'pencil': the concurrency graph on R is a matching, every matched pair meets at a point off the ovoid O,
               and (optional cap) at most CAP matched pairs.
usage: sa.py mode iters seed [cap]   -> prints best feasible size, writes set_sa_<mode>_<size>.json"""
import sys, json, math, random
from setup_common import *

NL = G.nl
oset = set(OV)
CON = G.con.astype(np.int32)
# meeting point of concurrent lines
MEET = {}
for z in range(N):
    ls = [l for l in range(NL) if G.I[z, l]]
    for i in range(len(ls)):
        for j in range(i + 1, len(ls)):
            MEET[(ls[i], ls[j])] = z
    # (pairs only)
ONOV = np.zeros((NL, NL), dtype=np.int32)      # 1 if the two lines meet on the ovoid
for (a, b), z in MEET.items():
    if z in oset:
        ONOV[a, b] = ONOV[b, a] = 1


def violations(R, mode, cap):
    x = np.zeros(NL, dtype=np.int32); x[list(R)] = 1
    deg = CON @ x                                   # R-neighbours of each line
    inR = x.astype(bool)
    if mode == 'spread':
        return int((deg[inR]).sum()) // 2
    v = int(np.maximum(deg[inR] - 1, 0).sum())
    pairs_idx = np.nonzero(inR & (deg == 1))[0]
    onov = 0
    pairs = 0
    for l in pairs_idx:
        m = int(np.nonzero(CON[l] * x)[0][0])
        if l < m:
            pairs += 1
            if ONOV[l, m]:
                onov += 1
    v += onov
    if cap is not None:
        v += max(0, pairs - cap)
    return v


def run(mode, iters, seed, cap=None, lam=1.5):
    rng = random.Random(seed)
    best = []
    R = set()
    x = np.zeros(NL, dtype=np.int32)
    cur_v = 0
    T0, T1 = 1.0, 0.02
    for it in range(iters):
        T = T0 * (T1 / T0) ** (it / iters)
        l = rng.randrange(NL)
        if l in R:
            R2 = R - {l}
        else:
            R2 = R | {l}
        v2 = violations(R2, mode, cap)
        f1 = len(R) - lam * cur_v
        f2 = len(R2) - lam * v2
        if f2 >= f1 or rng.random() < math.exp((f2 - f1) / T):
            R, cur_v = R2, v2
            if cur_v == 0 and len(R) > len(best):
                best = sorted(R)
    return best


if __name__ == '__main__':
    mode, iters, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else None
    best = run(mode, iters, seed, cap)
    assert violations(best, mode, cap) == 0
    if mode == 'spread':
        assert is_partial_spread(G, best)
    S = set(best)
    pairs = [[int(a), int(b), int(z)] for (a, b), z in MEET.items() if a in S and b in S]
    print(mode, 'cap', cap, 'seed', seed, 'best feasible size', len(best), 'matched pairs', len(pairs), flush=True)
    json.dump(dict(lines=best, pairs=pairs), open('set_sa_%s_%d_%s_s%d.json' % (mode, len(best), cap, seed), 'w'))

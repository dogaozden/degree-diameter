import sys, time, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r1/c46')
import anat
from anat import *
from collections import deque

def neighbors(S):
    out = []
    for j in (1, 2, 3):
        for v in range(1, anat.N):
            if v in S: continue
            new = list(S); new[j] = v; out.append(new)
    return np.array(out, dtype=np.int32)

def tabu(restricted, seed, secs, TL=60):
    rnd = random.Random(seed)
    def rand_state():
        while True:
            S = [0] + rnd.sample(range(1, anat.N), 3)
            if not restricted or girth_viol(np.array([S], dtype=np.int32))[0] == 0:
                return S
    cur = rand_state()
    best = (10**9, None)
    tabu_q = deque(maxlen=TL); tabu_s = set()
    t0 = time.time(); steps = 0; evals = 0
    while time.time() - t0 < secs:
        nb = neighbors(cur)
        c = lift_cost(nb); evals += len(nb)
        if restricted:
            gv = girth_viol(nb)
            eff = c + 1000 * (gv > 0)
        else:
            eff = c.copy()
        keys = [tuple(sorted(r)) for r in nb.tolist()]
        for i, k in enumerate(keys):
            if k in tabu_s: eff[i] += 500
        # ties: random tie-break
        mn = eff.min(); cand = np.flatnonzero(eff == mn)
        i = int(cand[rnd.randrange(len(cand))])
        cur = nb[i].tolist()
        tabu_q.append(keys[i]); tabu_s.add(keys[i])
        if len(tabu_q) == TL:
            old = tabu_q[0]
        steps += 1
        if (restricted and eff[i] < 1000) or (not restricted):
            if c[i] < best[0]:
                best = (int(c[i]), cur[:])
        if best[0] == 0: break
        # keep tabu set consistent with the queue
        if len(tabu_s) > TL:
            tabu_s = set(tabu_q)
    return best, steps, evals, time.time() - t0

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'near':
        setup('meta 55 20 2')
        S = np.array([[0, 929, 1084, 684]], dtype=np.int32)
        print('near55 girth_viol', girth_viol(S))
        setup('meta 137 8 10')
        S2 = np.array([[0, 1075, 3, 172]], dtype=np.int32)
        ca, cb = coverage(S2)
        print('near137 cost A', ca[0], 'B', cb[0], 'lift', lift_cost(S2)[0], 'girth_viol', girth_viol(S2))
        for r in level_stats(S2[0]):
            print('  near137 level t=%d walks=%d new=%d waste=%d closed=%d' % r)
    if mode == 'sample':
        setup('meta 55 20 2')
        rnd = np.random.default_rng(1)
        M = 20000
        S = np.zeros((M, 4), dtype=np.int32)
        for i in range(M):
            S[i, 1:] = rnd.choice(np.arange(1, anat.N), 3, replace=False)
        c = lift_cost(S); gv = girth_viol(S)
        g8 = gv == 0
        print('sample M=%d  girth>=8 fraction %.3f' % (M, g8.mean()))
        for name, mask in (('girth>=8', g8), ('girth<8', ~g8)):
            cc = c[mask]
            print(name, 'count', mask.sum(), 'min', cc.min(), 'median', np.median(cc), 'mean %.1f' % cc.mean(), 'frac cost<=5 %.4f' % (cc <= 5).mean())
        print('hist cost<=10 overall', np.bincount(c[c <= 10]).tolist())
        print('hist cost<=10 girth>=8', np.bincount(c[g8 & (c <= 10)], minlength=11).tolist())
    if mode == 'tabu':
        restricted = sys.argv[2] == '1'; seed = int(sys.argv[3]); secs = float(sys.argv[4])
        setup('meta 55 20 2')
        best, steps, evals, wall = tabu(restricted, seed, secs)
        print('TABU restricted=%d seed=%d best=%d steps=%d evals=%d wall=%.1f S=%s' % (restricted, seed, best[0], steps, evals, wall, best[1]))
        if best[1] is not None:
            write_edges(best[1], HERE + '/tabu_r%d_s%d.edges' % (restricted, seed))
            print('written', HERE + '/tabu_r%d_s%d.edges' % (restricted, seed))

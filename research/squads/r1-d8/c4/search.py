"""Random restarts + hill climbing on K-orbit labels (c4 card). usage: search.py which k seconds seed nsrc"""
import json
import os
import random
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from c4lib import Sym, run_liftw  # noqa: E402

which = sys.argv[1]
k = int(sys.argv[2])
secs = float(sys.argv[3])
seed = int(sys.argv[4])
nsrc = int(sys.argv[5])  # number of weighted sources sampled for the search (0 = all)
TVEC = (1, 2)
M1, M2 = 5, k
rng = random.Random(seed)
S = Sym(5, which)
ok, npo, nlo = S.stab_summary()
print('sym', which, 'K order', S.nK, 'point orbits', npo, 'line orbits', nlo, 'stab types match', ok, flush=True)
src_all = S.sources()
srcf = os.path.join(HERE, 'src_%s_%d_%d.txt' % (which, seed, nsrc))
base = os.path.join(HERE, 'base_%s_%d_%d_k%d.txt' % (which, seed, nsrc, k))
if nsrc and nsrc < len(src_all):
    src = rng.sample(src_all, nsrc)
else:
    src = src_all
S.write_srcs(srcf, src)


def evaluate(s_list, labels):
    S.write_base(base, s_list, labels, M1, M2, TVEC)
    return run_liftw(base, srcf)[0]


t0 = time.time()
best = None
restart = 0
log = open(os.path.join(HERE, 'search_log_%s_k%d_s%d.txt' % (which, k, seed)), 'w')
while time.time() - t0 < secs:
    restart += 1
    s_list = [S.matching(rng), S.matching(rng)]
    labels = [[rng.randrange(k) for _ in range(S.nporb)] for _ in range(2)]
    cur = evaluate(s_list, labels)
    stall = 0
    rstart_best = cur
    while time.time() - t0 < secs and cur > 0 and stall < 400:
        h = rng.randrange(2)
        O = rng.randrange(S.nporb)
        old = labels[h][O]
        labels[h][O] = (old + rng.randrange(1, k)) % k
        val = evaluate(s_list, labels)
        if val <= cur:
            if val < cur:
                stall = 0
            else:
                stall += 1
            cur = val
        else:
            labels[h][O] = old
            stall += 1
    msg = 'restart %d final_unr_sample %d time %.1f' % (restart, cur, time.time() - t0)
    print(msg, flush=True)
    log.write(msg + '\n'); log.flush()
    if best is None or cur < best[0]:
        best = (cur, [list(map(int, l)) for l in labels], [s.tolist() for s in s_list])
    if cur == 0:
        break
print('BEST sampled unr', best[0], 'restarts', restart, flush=True)
with open(os.path.join(HERE, 'best_%s_k%d_s%d_n%d.json' % (which, k, seed, nsrc)), 'w') as fh:
    json.dump({'unr_sampled': best[0], 'labels': best[1], 's': best[2], 'k': k, 'which': which, 'TVEC': TVEC}, fh)

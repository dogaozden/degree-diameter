"""Does quotient balance predict which metacyclic groups solve?  Data: every 'run' line of the voltage-lifts Haar
sweeps (research/lifts/runs/hc*_d*.tsv on branch claude/voltage-lifts-search-6lfotq): cell, N, group, seed, best cost.

Features per group (random S, 120 samples, e in S):
  fail_Q   = fraction of random S that already violate the rigorous quotient bound at some quotient Q_d
             (d = 1 or a prime d | m with d*k <= 20000);
  excess_Q = median over random S of max_d mu_d / mu_unif (how much worse than an even spread the best-balanced
             quotient picture is).
  mu       = N exp(-W/N) per condition (the size-law quantity; depends on N only).
Output: runs/predict_out.txt (one line per run, then a summary by mu bands).
"""
import glob
import os
import random
import re
import subprocess
import sys
from math import exp

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fibers import prime_factors, stats  # noqa: E402

VL = os.environ.get('VL', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/vl/research/lifts/runs')


def W_total(Delta, D):
    if D % 2 == 0:
        return sum(Delta * (Delta - 1) ** (l - 1) for l in range(1, D, 2))
    return 1 + sum(Delta * (Delta - 1) ** (l - 1) for l in range(2, D, 2))


def main():
    random.seed(7)
    runs = []
    for f in sorted(glob.glob(os.path.join(VL, 'hc*_d*D*.tsv'))):
        mm = re.search(r'_d(\d+)D(\d+)', f)
        Delta, D = int(mm.group(1)), int(mm.group(2))
        for line in open(f):
            if not line.startswith('run'):
                continue
            p = line.split('\t')
            g = p[2].split()
            if g[0] != 'meta' or g[4] != '1':
                continue
            best = int(p[4].split('=')[1])
            runs.append((Delta, D, int(p[1]), int(g[1]), int(g[2]), int(g[3]), best))
    feats = {}
    out = open(os.path.join(HERE, 'runs', 'predict_out.txt'), 'w')
    print('Delta D N m k r | best | mu | fail_Q excess_Q', file=out)
    rows = []
    for (Delta, D, N, m, k, r, best) in runs:
        key = (Delta, D, m, k, r)
        if key not in feats:
            ds = [1] + [d for d in prime_factors(m) if d < m and d * k <= 20000]
            fails, excs = 0, []
            for _ in range(120):
                T = [(0, 0)] + [(random.randrange(m), random.randrange(k)) for _ in range(Delta - 1)]
                worst, bad = 1.0, False
                for d in ds:
                    sl, mu_d, mu_u = stats(m, k, r, T, D, d)
                    bad |= sl < 1
                    worst = max(worst, mu_d / mu_u)
                fails += bad
                excs.append(worst)
            feats[key] = (fails / 120, float(np.median(excs)))
        W = W_total(Delta, D)
        nc = 1 if D % 2 == 0 else 2
        mu = nc * N * exp(-W / N)
        fq, ex = feats[key]
        rows.append((Delta, D, N, m, k, r, best, mu, fq, ex))
        print(f'{Delta} {D} {N} {m} {k} {r} | {best} | {mu:.1f} | {fq:.2f} {ex:.3f}', file=out, flush=True)
    # summary: within each cell, compare solved vs stalled
    print('\nper cell: solved runs vs stalled runs (median fail_Q, median excess_Q, median mu)', file=out)
    for cell in sorted({(r[0], r[1]) for r in rows}):
        sv = [r for r in rows if (r[0], r[1]) == cell and r[6] == 0]
        st = [r for r in rows if (r[0], r[1]) == cell and r[6] > 0]
        f = lambda L, i: (np.median([x[i] for x in L]) if L else float('nan'))
        print(f'{cell}: solved {len(sv)}: fail_Q {f(sv,8):.2f} excess {f(sv,9):.3f} mu {f(sv,7):.1f} | '
              f'stalled {len(st)}: fail_Q {f(st,8):.2f} excess {f(st,9):.3f} mu {f(st,7):.1f}', file=out)
    out.close()
    print(open(os.path.join(HERE, 'runs', 'predict_out.txt')).read()[-3000:])


if __name__ == '__main__':
    main()

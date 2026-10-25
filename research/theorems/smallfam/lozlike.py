"""Loz-like metacyclic candidates: Z_p x|_r Z_k (p prime) with small multiplier index c = (p-1)/o, a small central
part t = k/o and action order o >= OMIN, for N = p k in [NMIN, NMAX]; one r per order (frob_scan.actions).  Each is
annealed with hanneal (table built in numpy).  The shape of Loz's (4,9) group Z71 x| Z35 (c = 2, t = 1).
Usage: SCRATCH=dir python3 lozlike.py DELTA D NMIN NMAX [--cmax 3] [--tmax 3] [--omin 10] [--secs 30] [--seeds 2] [--list]
Output: <OUTDIR or runs>/lozlike_d{DELTA}D{D}.tsv: N p k r o c t costs best_set
"""
import argparse
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from frob_scan import actions, primes_upto  # noqa: E402

SP = os.environ.get('SCRATCH', '/tmp')


def table(m, k, r, path):
    """Z_m x|_r Z_k, element a*k + j, (a, j)(b, l) = (a + r^j b, j + l); same layout as hx.c 'meta'."""
    N = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N)
    a, j = idx // k, idx % k
    with open(path, 'w') as f:
        f.write(f'{N} 0\n')
        for x in range(N):
            ax, jx = divmod(x, k)
            row = ((ax + rp[jx] * a) % m) * k + (jx + j) % k
            f.write(' '.join(map(str, row.tolist())) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--cmax', type=int, default=3)
    ap.add_argument('--tmax', type=int, default=3)
    ap.add_argument('--omin', type=int, default=10)
    ap.add_argument('--secs', type=float, default=30)
    ap.add_argument('--seeds', type=int, default=2)
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()
    cands = []
    for p in primes_upto(a.nmax):
        for k in range(2, a.nmax // p + 1):
            N = p * k
            if not (a.nmin <= N <= a.nmax):
                continue
            for r, o in actions(p, k):
                c, t = (p - 1) // o, k // o
                if c <= a.cmax and t <= a.tmax and o >= a.omin:
                    cands.append((N, p, k, r, o, c, t))
    cands.sort()
    if a.list:
        for x in cands:
            print(*x)
        print(len(cands), 'candidates')
        return
    outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'lozlike_d{a.Delta}D{a.D}.tsv')
    done = set()
    if os.path.exists(outp):
        done = {tuple(map(int, l.split('\t')[1:4])) for l in open(outp) if l[0].isdigit()}
    log = open(outp, 'a')
    for (N, p, k, r, o, c, t) in cands:
        if (p, k, r) in done:
            continue
        tab = os.path.join(SP, f'll_{p}_{k}_{r}.txt')
        table(p, k, r, tab)
        costs, bset = [], '-'
        for s in range(1, a.seeds + 1):
            out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                                  os.path.join(SP, f'll_sol_{p}_{k}_{r}_{s}.txt')], capture_output=True, text=True).stdout
            res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
            best = int(res[4].split('=')[1])
            if not costs or best < min(costs):
                bset = ' '.join(res[res.index('best_set') + 1:])
            costs.append(best)
            if best == 0:
                print(f'*** Z{p} x|_{r} Z{k} (N={N}, o={o}): cost 0, S = {bset}', flush=True)
                break
        log.write(f'{N}\t{p}\t{k}\t{r}\t{o}\t{c}\t{t}\t{",".join(map(str, costs))}\t{bset}\n')
        log.flush()
        os.remove(tab)


if __name__ == '__main__':
    main()

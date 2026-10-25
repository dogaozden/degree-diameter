"""Second stage of fscreen.py: longer anneals for the groups the first stage left at low cost.

Reads an fscreen tsv, takes every group whose lowest first-stage cost is <= THRESH, re-exports it (generator
permutations + gtab) and runs hanneal for SECS seconds with seeds 2..SEEDS+1.
Output: <OUTDIR or runs>/fscreen2_d{DELTA}D{D}{TAG}.tsv: n id stage1_cost stage2_costs best_set.
Usage: SCRATCH=dir python3 fscreen2.py DELTA D TSV [--thresh 4] [--secs 30] [--seeds 2] [--par 3] [--tag T]
"""
import argparse
import os
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fscreen import export_gens  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('tsv')
    ap.add_argument('--thresh', type=int, default=4)
    ap.add_argument('--secs', type=float, default=30)
    ap.add_argument('--seeds', type=int, default=2)
    ap.add_argument('--par', type=int, default=3)
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    cand = []
    for line in open(a.tsv):
        f = line.rstrip('\n').split('\t')
        if len(f) < 8 or not f[0].isdigit() or f[6] == '-':
            continue
        c = min(int(x) for x in f[6].split(','))
        if c <= a.thresh:
            cand.append((int(f[0]), int(f[1]), c))
    outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'fscreen2_d{a.Delta}D{a.D}{a.tag}.tsv')
    done = set()
    if os.path.exists(outp):
        done = {(int(l.split('\t')[0]), int(l.split('\t')[1])) for l in open(outp) if l[0].isdigit()}
    cand = [c for c in cand if (c[0], c[1]) not in done]
    print(f'{len(cand)} groups with stage-1 cost <= {a.thresh}', flush=True)
    log = open(outp, 'a')
    pool = ThreadPoolExecutor(a.par)
    byorder = {}
    for (n, i, c) in cand:
        byorder.setdefault(n, []).append((i, c))
    futs = []
    for n, lst in sorted(byorder.items()):
        paths = export_gens(n, [i for i, _ in lst])
        for (i, c) in lst:
            futs.append((pool.submit(run_one2, n, i, paths[i], a), c))
    for fu, c in futs:
        n, i, st, res = fu.result()
        if st != 'ok':
            log.write(f'{n}\t{i}\t{c}\t{st}\t-\n')
        else:
            costs, bset = res
            log.write(f'{n}\t{i}\t{c}\t{",".join(map(str, costs))}\t{bset}\n')
            if min(costs) == 0:
                print(f'*** {n} {i}: cost 0, S = {bset}', flush=True)
        log.flush()
    pool.shutdown()


def run_one2(n, i, gpath, a):
    # seeds 2.. (stage 1 used seed 1): shift by renaming through run_one's seed loop
    import subprocess
    tab = gpath.replace('gens_', 'tabf2_')
    r = subprocess.run([os.path.join(HERE, 'gtab'), gpath, tab], capture_output=True, text=True)
    os.remove(gpath)
    if r.returncode != 0:
        return n, i, 'gtab-failed', []
    costs, bset = [], '-'
    sp = os.path.dirname(gpath)
    for s in range(2, a.seeds + 2):
        out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                              os.path.join(sp, f'f2sol_{n}_{i}_{s}.txt')], capture_output=True, text=True).stdout
        res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
        best = int(res[4].split('=')[1])
        if not costs or best < min(costs):
            bset = ' '.join(res[res.index('best_set') + 1:])
        costs.append(best)
        if best == 0:
            break
    os.remove(tab)
    return n, i, 'ok', (costs, bset)


if __name__ == '__main__':
    main()

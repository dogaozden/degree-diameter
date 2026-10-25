"""Fast annealing screen of voltage lifts of a small base over ALL groups of given orders (GAP SmallGroups).

As lscreen.py (lanneal on every group, rigorous filters only: rank of G/G' <= free voltages, |G^ab| <= the lattice
bound of liftbound.py), but batched like fscreen.py: one GAP process per batch exports generator permutations,
gtab rebuilds the table, and PAR workers anneal while GAP exports the next batch.
Output: <OUTDIR or runs>/flscreen_<base>_D<D><TAG>.tsv: n id - |G^ab| cost(s) voltages
Usage: SCRATCH=dir python3 flscreen.py BASE D NMIN NMAX [--secs 3] [--seeds 1] [--par 3] [--batch 40] [--maxgroups 2000] [--skip ...]
"""
import argparse
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from math import prod

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import SP, gap, list_groups  # noqa: E402
from fscreen import export_gens  # noqa: E402


def run_one(n, i, gpath, base, D, secs, seeds):
    if not os.path.exists(gpath):
        return n, i, 'export-failed', None
    tab = gpath.replace('gens_', 'ltab_')
    r = subprocess.run([os.path.join(HERE, 'gtab'), gpath, tab], capture_output=True, text=True)
    os.remove(gpath)
    if r.returncode != 0:
        return n, i, 'gtab-failed', None
    costs, vb = [], '-'
    for s in range(1, seeds + 1):
        out = subprocess.run([os.path.join(HERE, 'lanneal'), tab, base, str(D), str(secs), str(s), '8',
                              os.path.join(SP, f'flsol_{n}_{i}_{s}.txt')], capture_output=True, text=True).stdout
        res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
        best = int(res[4].split('=')[1])
        if not costs or best < min(costs):
            vb = ' '.join(res[res.index('voltages') + 1:])
        costs.append(best)
        if best == 0:
            break
    os.remove(tab)
    return n, i, 'ok', (costs, vb)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('base')
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--secs', type=float, default=3)
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--par', type=int, default=3)
    ap.add_argument('--batch', type=int, default=40)
    ap.add_argument('--maxgroups', type=int, default=2000)
    ap.add_argument('--skip', default='')
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    skip = {int(x) for x in a.skip.split(',') if x}
    bname = os.path.splitext(os.path.basename(a.base))[0]
    nfree = sum(1 for l in open(a.base) if l.strip() and not l.startswith('#') and len(l.split()) == 2)
    lat = int(subprocess.run(['python3', os.path.join(HERE, 'liftbound.py'), a.base, str(a.D)],
                             capture_output=True, text=True).stdout.split('<=')[-1])
    outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'flscreen_{bname}_D{a.D}{a.tag}.tsv')
    done = set()
    if os.path.exists(outp):
        done = {(l.split('\t')[0], l.split('\t')[1]) for l in open(outp) if l[0].isdigit()}
    log = open(outp, 'a')
    pool = ThreadPoolExecutor(a.par)
    pending = []

    def drain(block):
        nonlocal pending
        keep = []
        for fu, ab in pending:
            if block or fu.done():
                n, i, st, res = fu.result()
                if st != 'ok':
                    log.write(f'{n}\t{i}\t-\t|G^ab|={ab}\t{st}\t-\n')
                else:
                    costs, vb = res
                    log.write(f'{n}\t{i}\t-\t|G^ab|={ab}\t{",".join(map(str, costs))}\t{vb}\n')
                    if min(costs) == 0:
                        print(f'*** {n} {i}: lift of {bname} cost 0, voltages {vb}', flush=True)
                log.flush()
            else:
                keep.append((fu, ab))
        pending = keep

    for n in range(a.nmin, a.nmax + 1):
        if n in skip or (str(n), '*') in done:
            continue
        out = gap(f'if SmallGroupsAvailable({n}) then Print(NrSmallGroups({n}), "\\n"); else Print("-1\\n"); fi; QUIT;\n', 600)
        nr = int(out.split()[0])
        if nr < 0 or nr > a.maxgroups:
            log.write(f'{n}\t*\t-\t-\tskipped-order({nr} groups)\t-\n'); log.flush()
            continue
        todo = []
        for (i, dsize, inv) in list_groups(n):
            if (str(n), str(i)) in done:
                continue
            ab = prod(inv) if inv else 1
            if len([x for x in inv if x > 1]) > nfree:
                log.write(f'{n}\t{i}\t-\t|G^ab|={ab}\trank>{nfree}\t-\n'); continue
            if ab > lat:
                log.write(f'{n}\t{i}\t-\t|G^ab|={ab}\tabfail(>{lat})\t-\n'); continue
            todo.append((i, ab))
        log.flush()
        for b in range(0, len(todo), a.batch):
            chunk = todo[b:b + a.batch]
            while len(pending) > 2 * a.batch:
                drain(False)
                if len(pending) > 2 * a.batch:
                    time.sleep(0.5)
            paths = export_gens(n, [c[0] for c in chunk])
            for (i, ab) in chunk:
                pending.append((pool.submit(run_one, n, i, paths[i], a.base, a.D, a.secs, a.seeds), ab))
            drain(False)
    drain(True)
    pool.shutdown()


if __name__ == '__main__':
    main()

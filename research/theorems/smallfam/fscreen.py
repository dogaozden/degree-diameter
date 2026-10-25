"""Fast annealing screen of Haar graphs over ALL groups of given orders (GAP SmallGroups), with rigorous filters only.

Same filters and annealer as screen.py, but much cheaper per group:
  - one GAP process per batch of groups exports only the right-multiplication permutations of a small generating set
    (t*N lookups instead of the N^2 of a full table); gtab rebuilds the table in C;
  - a pool of PAR workers runs hanneal (SECS seconds per seed) while GAP exports the next batch.
Filters (rigorous, as allgroups.py): the abelianization needs at most DELTA-1 generators, and abfilt's
abelianization bound. No heuristic skips.
Output: runs/fscreen_d{DELTA}D{D}{TAG}.tsv: n id - abinv |G'| filter costs best_set (structure is filled in later
for the interesting groups). A cost-0 line is a solution claim: rebuild and check it (onegroup.py / apsp).
Usage: SCRATCH=dir python3 fscreen.py DELTA D NMIN NMAX [--secs 5] [--seeds 1] [--par 3] [--batch 40] [--maxgroups 2000]
"""
import argparse
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from math import prod

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import SP, abfilt, gap, list_groups  # noqa: E402


def export_gens(n, ids, timeout=3600):
    paths = {i: os.path.join(SP, f'gens_{n}_{i}.txt') for i in ids}
    script = f'''for i in [{",".join(map(str, ids))}] do
  GRP := SmallGroup({n}, i);; el := AsSSortedList(GRP);; nn := Length(el);; gs := SmallGeneratingSet(GRP);;
  f := OutputTextFile(Concatenation("{SP}/gens_{n}_", String(i), ".txt.tmp"), false);; SetPrintFormattingStatus(f, false);;
  AppendTo(f, nn, " ", Position(el, One(GRP)) - 1, " ", Length(gs), "\\n");;
  for g in gs do AppendTo(f, JoinStringsWithSeparator(List(el, x -> String(Position(el, x * g) - 1)), " "), "\\n");; od;
  CloseStream(f);; Exec(Concatenation("mv {SP}/gens_{n}_", String(i), ".txt.tmp {SP}/gens_{n}_", String(i), ".txt"));
od; QUIT;
'''
    gap(script, timeout)
    return paths


def run_one(n, i, gpath, Delta, D, secs, seeds):
    if not os.path.exists(gpath):
        return n, i, 'export-failed', []
    tab = gpath.replace('gens_', 'tabf_')
    r = subprocess.run([os.path.join(HERE, 'gtab'), gpath, tab], capture_output=True, text=True)
    os.remove(gpath)
    if r.returncode != 0:
        return n, i, 'gtab-failed:' + r.stderr.strip(), []
    costs, bset = [], '-'
    for s in range(1, seeds + 1):
        out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(Delta), str(D), str(secs), str(s), '8',
                              os.path.join(SP, f'fsol_{n}_{i}_{s}.txt')], capture_output=True, text=True).stdout
        res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
        best = int(res[4].split('=')[1])
        if not costs or best < min(costs):
            bset = ' '.join(res[res.index('best_set') + 1:])
        costs.append(best)
        if best == 0:
            break
    os.remove(tab)
    return n, i, 'ok', (costs, bset)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--secs', type=float, default=5)
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--par', type=int, default=3)
    ap.add_argument('--batch', type=int, default=40)
    ap.add_argument('--maxgroups', type=int, default=2000)
    ap.add_argument('--skip', default='')
    ap.add_argument('--orders', default='', help='comma-separated explicit orders (overrides the range)')
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    skip = {int(x) for x in a.skip.split(',') if x}
    orders = [int(x) for x in a.orders.split(',') if x] or list(range(a.nmin, a.nmax + 1))
    outp = os.path.join(HERE, 'runs', f'fscreen_d{a.Delta}D{a.D}{a.tag}.tsv')
    done = set()
    if os.path.exists(outp):
        for line in open(outp):
            f = line.split('\t')
            if len(f) > 2 and f[0].isdigit():
                done.add((int(f[0]), f[1]))
    log = open(outp, 'a')
    pool = ThreadPoolExecutor(a.par)
    pending = []

    def drain(block):
        nonlocal pending
        keep = []
        for fu, meta in pending:
            if block or fu.done():
                n, i, st, res = fu.result()
                inv, dsize, fr = meta
                if st != 'ok':
                    log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\t{st}\t-\t-\n')
                else:
                    costs, bset = res
                    log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\t{fr}\t{",".join(map(str, costs))}\t{bset}\n')
                    if min(costs) == 0:
                        print(f'*** {n} {i}: cost 0, S = {bset}', flush=True)
                log.flush()
            else:
                keep.append((fu, meta))
        pending = keep

    for n in orders:
        if n in skip or (n, '*') in done:
            continue
        nr = int(gap(f'Print(NrSmallGroups({n}), "\\n"); QUIT;\n', 600).split()[0])
        if nr > a.maxgroups:
            log.write(f'{n}\t*\t-\t-\t-\tskipped-order({nr} groups)\t-\t-\n'); log.flush()
            continue
        todo = []
        for (i, dsize, inv) in list_groups(n):
            if (n, str(i)) in done:
                continue
            ninv = len([x for x in inv if x > 1])
            if ninv > a.Delta - 1:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\trank>{a.Delta-1}\t-\t-\n'); continue
            fr = abfilt(a.Delta, a.D, dsize, inv)
            if fr.startswith('pass 0 '):
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tabfail\t-\t-\n'); continue
            todo.append((i, dsize, inv, fr))
        log.flush()
        for b in range(0, len(todo), a.batch):
            chunk = todo[b:b + a.batch]
            while len(pending) > 2 * a.batch:          # bound the queue (gens files on disk)
                drain(False)
                if len(pending) > 2 * a.batch:
                    import time; time.sleep(0.5)
            paths = export_gens(n, [c[0] for c in chunk])
            for (i, dsize, inv, fr) in chunk:
                fu = pool.submit(run_one, n, i, paths[i], a.Delta, a.D, a.secs, a.seeds)
                pending.append((fu, (inv, dsize, fr)))
            drain(False)
    drain(True)
    pool.shutdown()


if __name__ == '__main__':
    main()

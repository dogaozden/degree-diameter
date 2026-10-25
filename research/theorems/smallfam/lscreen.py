"""Annealing screen of voltage lifts of a small base over all groups of given orders (GAP SmallGroups).
Filters: rank of G/G' <= number of free voltages; KMIN <= |G/G'| <= KMAX (heuristic); |G^ab| <= lattice bound
(liftbound.py, rigorous).  Then lanneal for SECS per seed.  Output: runs/lscreen_<base>_D<D>.tsv.
Usage: python3 lscreen.py BASE D NMIN NMAX [--secs 30] [--seeds 1] [--abmin 2] [--abmax 48] [--maxgroups 400]"""
import argparse, os, subprocess, sys
from math import prod
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import SP, gap, list_groups  # noqa: E402
from screen import export_table  # noqa: E402
ap = argparse.ArgumentParser()
ap.add_argument('base'); ap.add_argument('D', type=int); ap.add_argument('nmin', type=int); ap.add_argument('nmax', type=int)
ap.add_argument('--secs', type=float, default=30); ap.add_argument('--seeds', type=int, default=1)
ap.add_argument('--abmin', type=int, default=2); ap.add_argument('--abmax', type=int, default=48)
ap.add_argument('--maxgroups', type=int, default=400)
a = ap.parse_args()
bname = os.path.splitext(os.path.basename(a.base))[0]
nfree = sum(1 for l in open(a.base) if l.strip() and not l.startswith('#') and len(l.split()) == 2)
lat = int(subprocess.run(['python3', os.path.join(HERE, 'liftbound.py'), a.base, str(a.D)], capture_output=True, text=True).stdout.split('<=')[-1])
outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'lscreen_{bname}_D{a.D}.tsv')
done = set()
if os.path.exists(outp):
    for l in open(outp):
        f = l.split('\t')
        if len(f) > 2 and f[1].isdigit(): done.add((int(f[0]), int(f[1])))
log = open(outp, 'a')
for n in range(a.nmin, a.nmax + 1):
    nr = int(gap(f'Print(NrSmallGroups({n}), "\\n"); QUIT;\n', 600).split()[0])
    if nr > a.maxgroups:
        log.write(f'{n}\t*\tskipped-order({nr} groups)\n'); log.flush(); continue
    for (i, dsize, inv) in list_groups(n):
        if (n, i) in done: continue
        ab = prod(inv) if inv else 1
        if len([x for x in inv if x > 1]) > nfree:
            log.write(f'{n}\t{i}\t-\trank>{nfree}\n'); log.flush(); continue
        if ab > lat:
            log.write(f'{n}\t{i}\t-\tabfail(|G^ab|={ab}>{lat})\n'); log.flush(); continue
        if ab < a.abmin or ab > a.abmax:
            log.write(f'{n}\t{i}\t-\theuristic-skip(|G^ab|={ab})\n'); log.flush(); continue
        struct, tab = export_table(n, i)
        costs, vb = [], '-'
        for s in range(1, a.seeds + 1):
            r = subprocess.run([os.path.join(HERE, 'lanneal'), tab, a.base, str(a.D), str(a.secs), str(s), '8',
                                os.path.join(SP, f'ls_sol_{bname}_{n}_{i}_{s}.txt')], capture_output=True, text=True).stdout
            res = [l for l in r.splitlines() if l.startswith('RESULT')][0].split()
            best = int(res[4].split('=')[1]); costs.append(best)
            if best == min(costs): vb = ' '.join(res[res.index('voltages') + 1:])
            if best == 0:
                print(f'*** {n} {i} {struct}: lift of {bname} cost 0, voltages {vb}', flush=True); break
        log.write(f'{n}\t{i}\t{struct}\t|G^ab|={ab}\t{",".join(map(str, costs))}\t{vb}\n'); log.flush()
        os.remove(tab)

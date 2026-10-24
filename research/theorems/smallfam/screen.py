"""Broad annealing screen of Haar graphs over all groups of given orders (GAP SmallGroups).

For each group: rank and abelianization filters (as allgroups.py); GAP export of the multiplication table only (no
automorphism group, no plan); hanneal for SECS seconds per seed.  A group that reaches cost 0 is a solution (check it
with hx/apsp); low-cost groups are candidates for the exhaustive search of allgroups.py / named.py.
Output: runs/screen_d{DELTA}D{D}{TAG}.tsv: n id structure abinv |G'| filter best_cost (per seed) best_set
Usage: python3 screen.py DELTA D NMIN NMAX [--secs 20] [--seeds 1] [--maxgroups 2000] [--tag T]
"""
import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import SP, abfilt, gap, list_groups  # noqa: E402


def export_table(n, i, timeout=1200):
    tab = os.path.join(SP, f'scr_tab_{n}_{i}_{os.getpid()}.txt')
    script = f'''GRP := SmallGroup({n}, {i});; el := AsSSortedList(GRP);; nn := Length(el);;
Print(StructureDescription(GRP), "\\n");
f := OutputTextFile("{tab}", false);; SetPrintFormattingStatus(f, false);;
AppendTo(f, nn, " ", Position(el, One(GRP)) - 1, "\\n");;
for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y -> String(Position(el, x * y) - 1)), " "), "\\n");; od;
CloseStream(f);; QUIT;
'''
    out = gap(script, timeout)
    return (out.strip().splitlines() or ['?'])[0], tab


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--secs', type=float, default=20)
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--maxgroups', type=int, default=2000)
    ap.add_argument('--tag', default='')
    ap.add_argument('--skip', default='', help='comma-separated orders to skip')
    ap.add_argument('--abmin', type=int, default=1, help='skip groups with |G/G\'| below this (dihedral-like types)')
    ap.add_argument('--abmaxorder', type=int, default=10**9, help='skip groups with |G/G\'| above this')
    a = ap.parse_args()
    skip = {int(x) for x in a.skip.split(',') if x}
    outp = os.path.join(HERE, 'runs', f'screen_d{a.Delta}D{a.D}{a.tag}.tsv')
    done = set()
    if os.path.exists(outp):
        for line in open(outp):
            f = line.split('\t')
            if len(f) > 2 and f[0].isdigit() and f[1].isdigit():
                done.add((int(f[0]), int(f[1])))
    log = open(outp, 'a')
    for n in range(a.nmin, a.nmax + 1):
        if n in skip:
            continue
        nr = int(gap(f'Print(NrSmallGroups({n}), "\\n"); QUIT;\n', 600).split()[0])
        if nr > a.maxgroups:
            log.write(f'{n}\t*\t-\t-\t-\tskipped-order({nr} groups)\t-\t-\n'); log.flush()
            continue
        for (i, dsize, inv) in list_groups(n):
            if (n, i) in done:
                continue
            ninv = len([x for x in inv if x > 1])
            if ninv > a.Delta - 1:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\trank>{a.Delta-1}\t-\t-\n'); log.flush()
                continue
            from math import prod
            ab = prod(inv) if inv else 1
            if ab < a.abmin or ab > a.abmaxorder:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\t|G/G\'|={ab} outside [{a.abmin},{a.abmaxorder}] (heuristic skip)\t-\t-\n'); log.flush()
                continue
            fr = abfilt(a.Delta, a.D, dsize, inv)
            if fr.startswith('pass 0 '):
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tabfail\t-\t-\n'); log.flush()
                continue
            struct, tab = export_table(n, i)
            costs, bset = [], '-'
            for s in range(1, a.seeds + 1):
                r = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                                    os.path.join(SP, f'scr_sol_{n}_{i}_{s}.txt')], capture_output=True, text=True).stdout
                res = [l for l in r.splitlines() if l.startswith('RESULT')][0].split()
                best = int(res[4].split('=')[1])
                costs.append(best)
                if best == min(costs):
                    bset = ' '.join(res[res.index('best_set') + 1:])
                if best == 0:
                    print(f'*** {n} {i} {struct}: cost 0, S = {bset}', flush=True)
                    break
            log.write(f'{n}\t{i}\t{struct}\t{inv}\t{dsize}\t{fr}\t{",".join(map(str, costs))}\t{bset}\n'); log.flush()
            os.remove(tab)


if __name__ == '__main__':
    main()

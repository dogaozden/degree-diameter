"""Card c5: take the lowest-cost (group, base) pair from the lscreen TSVs in OUTDIR, re-anneal it with lanneal
directly for 60 s with seeds 2 and 3, and, on cost 0, rebuild the lift with lift_edges.py and check it with
verify/apsp (must print RESULT VALID)."""
import glob
import os
import subprocess
import sys

C5 = '/home/user/degree-diameter/research/squads/r2-smallfam/c5'
SM = '/home/user/degree-diameter/research/theorems/smallfam'
os.environ.update(OUTDIR=C5, SCRATCH=C5 + '/tmp', THREADS='1')
sys.path.insert(0, SM)
from screen import export_table  # noqa: E402

rows = []
for f in sorted(glob.glob(f'{C5}/lscreen_b44_*_D9.tsv')):
    base = os.path.basename(f)[len('lscreen_'):-len('_D9.tsv')]
    for line in open(f):
        p = line.rstrip('\n').split('\t')
        if len(p) < 6 or not p[1].isdigit():
            continue
        try:
            costs = [int(x) for x in p[4].split(',')]
        except ValueError:
            continue
        rows.append((min(costs), base, int(p[0]), int(p[1]), p[2], p[5]))
rows.sort(key=lambda r: (r[0], r[1], r[2], r[3]))
print('lowest-cost screened pairs (cost, base, n, id, structure, voltages):', flush=True)
for r in rows[:12]:
    print('  ', r, flush=True)
if not rows:
    print('no screened rows', flush=True)
    sys.exit(0)

cost, base, n, i, struct, volts0 = rows[0]
print(f're-anneal {base} order {n} id {i} {struct} (screen cost {cost})', flush=True)
tab = export_table(n, i)[1]
for seed in (2, 3):
    out = f'{C5}/reanneal_{base}_{n}_{i}_s{seed}.sol'
    r = subprocess.run([f'{SM}/lanneal', tab, f'bases/{base}.txt', '9', '60', str(seed), '8', out],
                       cwd=SM, capture_output=True, text=True, timeout=200)
    res = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
    print(res[0] if res else ('no RESULT line: ' + r.stdout[-300:] + r.stderr[-300:]), flush=True)
    if not res:
        continue
    toks = res[0].split()
    best = int([t for t in toks if t.startswith('best=')][0].split('=')[1])
    volts = toks[toks.index('voltages') + 1:]
    if best == 0:
        edges = f'{C5}/lift_{base}_{n}_{i}_s{seed}.edges'
        subprocess.run(['python3', f'{SM}/lift_edges.py', str(n), str(i), f'bases/{base}.txt', edges] + volts,
                       cwd=SM, check=True)
        v = subprocess.run([f'{SM}/verify/apsp', edges, '3', '9'], cwd=SM, capture_output=True, text=True)
        print('VERIFY', edges, v.stdout.strip().splitlines()[-1:] or v.stderr[-300:], flush=True)
os.remove(tab)
print('reanneal done', flush=True)

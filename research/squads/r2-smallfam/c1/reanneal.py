"""c1 helper: take the k lowest-cost groups from the lscreen tsv, re-anneal each once with lanneal (one seed each).
Usage (cwd = smallfam, env OUTDIR and SCRATCH set): python3 reanneal.py K SECS SEED0
Writes $OUTDIR/reanneal.tsv: n, id, struct, screen_cost, seed, best, voltages (one line per run).
"""
import os, subprocess, sys
SM = '/home/user/degree-diameter/research/theorems/smallfam'
sys.path.insert(0, SM)
from screen import export_table  # noqa: E402

OUT = os.environ['OUTDIR']
SCR = os.environ['SCRATCH']
K, SECS, SEED0 = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
BASE = 'bases/b33_0.txt'
D = '10'

rows = []
for line in open(os.path.join(OUT, 'lscreen_b33_0_D10.tsv')):
    f = line.rstrip('\n').split('\t')
    if len(f) < 6 or not f[0].isdigit() or not f[1].isdigit():
        continue
    costs = [int(c) for c in f[4].split(',') if c.strip().isdigit()]
    if not costs:
        continue
    rows.append((min(costs), int(f[0]), int(f[1]), f[2], f[5].split()))
rows.sort(key=lambda r: (r[0], r[1], r[2]))
print(f'{len(rows)} screened groups with a cost; top {K}:', flush=True)
for r in rows[:K]:
    print('  screen cost', r[0], 'n', r[1], 'id', r[2], r[3], flush=True)

res_path = os.path.join(OUT, 'reanneal.tsv')
with open(res_path, 'a') as log:
    for k, (c0, n, i, struct, vb) in enumerate(rows[:K]):
        seed = SEED0 + k
        _, tab = export_table(n, i)
        r = subprocess.run([os.path.join(SM, 'lanneal'), tab, BASE, D, SECS, str(seed), '8',
                            os.path.join(SCR, f'ra_sol_{n}_{i}_{seed}.txt')],
                           cwd=SM, capture_output=True, text=True)
        os.remove(tab)
        line = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
        if not line:
            print('no RESULT for', n, i, r.stderr[-300:], flush=True)
            log.write(f'{n}\t{i}\t{struct}\t{c0}\t{seed}\tFAILED\t-\n'); log.flush()
            continue
        res = line[0].split()
        best = int(res[4].split('=')[1])
        volts = ' '.join(res[res.index('voltages') + 1:])
        print(f'RE {n} {i} {struct} seed {seed} best={best} voltages {volts}', flush=True)
        log.write(f'{n}\t{i}\t{struct}\t{c0}\t{seed}\t{best}\t{volts}\n'); log.flush()
        if best == 0:
            print('*** cost 0 found', n, i, struct, volts, flush=True)

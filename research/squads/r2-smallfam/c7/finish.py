"""c7 finish: lowest-cost (base, group) pair of the lift screen -> lanneal re-anneal (60 s, seeds 2-4, one at a time)
-> lift_edges.py + verify/apsp for any cost-0 lift -> one line in ../scoreboard.jsonl.
Usage: python3 finish.py  (uses only the TSVs in this folder; lanneal and apsp are the tools of the brief)."""
import glob
import json
import os
import subprocess
C7 = '/home/user/degree-diameter/research/squads/r2-smallfam/c7'
SMALL = '/home/user/degree-diameter/research/theorems/smallfam'
SB = '/home/user/degree-diameter/research/squads/r2-smallfam/scoreboard.jsonl'
ENV = dict(os.environ, OUTDIR=C7, SCRATCH=C7 + '/tmp', THREADS='1')
LOG = open(C7 + '/finish.log', 'a')


def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


rows, per_base = [], {}
for tsv in sorted(glob.glob(C7 + '/lscreen_b55_*_D7.tsv')):
    base = os.path.basename(tsv)[len('lscreen_'):-len('_D7.tsv')]
    cnt = 0
    for line in open(tsv):
        f = line.rstrip('\n').split('\t')
        if len(f) < 6 or not f[1].isdigit():
            continue
        cnt += 1
        costs = [int(x) for x in f[4].split(',')]
        rows.append((min(costs), base, int(f[0]), int(f[1]), f[2], f[3], f[5]))
    per_base[base] = cnt
rows.sort(key=lambda r: (r[0], r[1], r[2], r[3]))
say('pairs screened:', len(rows), 'per base:', per_base)
say('lowest screen costs:', [(r[0], r[1], f'{r[2]},{r[3]}', r[4]) for r in rows[:6]])
if not rows:
    raise SystemExit('nothing screened')
cost0, base, n, i, struct, ab, vb = rows[0]
say(f're-anneal pair: {base} group {n},{i} {struct} (screen cost {cost0})')


def verify(volts, tag):
    out = f'{C7}/lift_{base}_{n}_{i}_{tag}.edges'
    r = subprocess.run(['timeout', '1200', 'nice', '-n', '10', 'python3', SMALL + '/lift_edges.py', str(n), str(i),
                        f'{SMALL}/bases/{base}.txt', out] + [str(v) for v in volts],
                       cwd=SMALL, env=ENV, capture_output=True, text=True)
    say('lift_edges:', (r.stdout + r.stderr).strip()[-300:])
    v = subprocess.run(['timeout', '1200', 'nice', '-n', '10', SMALL + '/verify/apsp', out, '3', '7'],
                       cwd=SMALL, env=ENV, capture_output=True, text=True)
    txt = (v.stdout + v.stderr).strip()
    say('apsp:', txt[-300:])
    return 'RESULT VALID' in txt


def reanneal(seed):
    tab = f'{C7}/tmp/cache/{n}_{i}.tab'
    out = f'{C7}/reanneal_{base}_{n}_{i}_s{seed}.sol'
    r = subprocess.run(['timeout', '1200', 'nice', '-n', '10', SMALL + '/lanneal', tab, f'{SMALL}/bases/{base}.txt',
                        '7', '60', str(seed), '8', out], cwd=SMALL, env=ENV, capture_output=True, text=True)
    res = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
    if not res:
        say('no RESULT line for seed', seed, (r.stderr or '')[-200:])
        return None, None
    f = res[0].split()
    best = int(f[4].split('=')[1])
    volts = [int(x) for x in f[f.index('voltages') + 1:]]
    say(f'reanneal seed {seed}: {res[0]}')
    return best, volts


results = []
for seed in (2, 3, 4):
    b, v = reanneal(seed)
    if b is not None:
        results.append((b, seed, v))
min_cost = min([cost0] + [b for b, _, _ in results])
cands = []
if cost0 == 0:
    cands.append((list(map(int, vb.split())), 'screen'))
for b, seed, v in results:
    if b == 0:
        cands.append((v, f'seed{seed}'))
valid, how = False, ''
for volts, tag in cands:
    if verify(volts, tag):
        valid, how = True, tag
        break
say('min cost seen:', min_cost, '| valid:', valid, how)
line = {
    'card': 'c7',
    'idea': 'lscreen of the fifteen 5+5 bases over orders 17-25 (same lanneal screen, GAP tables cached), then 60 s re-anneals of the lowest-cost pair',
    'code': 'research/squads/r2-smallfam/c7/fastscreen.py',
    'command': 'cd research/theorems/smallfam && timeout 1200 nice -n 10 python3 .../c7/fastscreen.py bases/b55_K.txt 7 17 25 --secs 3 --abmin 1 --abmax 1000000 (K = 0..14, loop in c7/run_loop2.sh); re-anneal: lanneal TABLE bases/BASE.txt 7 60 SEED 8 OUT (seeds 2-4)',
    'score': 10 * n if valid else 0,
    'best_cost': min_cost,
    'best_group': f'{n},{i} {struct} and {base}',
    'cell': '(3,7)',
    'valid': valid,
    'next': 'screen the 5+5 bases over orders 17-25 with more seconds per group only for the lowest-cost pairs, and try the 6+6 bases at the same orders',
    'pairs_screened': f'{len(rows)} of {15 * 34}',
    'bases_started': sorted(per_base),
}
with open(SB, 'a') as fh:
    fh.write(json.dumps(line) + '\n')
say('scoreboard line appended:', json.dumps(line))

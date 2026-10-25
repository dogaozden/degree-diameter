"""c2 helper: re-anneal the two lowest-cost (base, group) pairs from the lscreen TSVs with lanneal, 60 s, seeds 2 and 3.
If a run reaches cost 0: rebuild the edge list with lift_edges.py and check it with verify/apsp (D = 10)."""
import os, subprocess, time
D = '/home/user/degree-diameter/research/squads/r2-smallfam/c2'
SM = '/home/user/degree-diameter/research/theorems/smallfam'
env = dict(os.environ, OUTDIR=D, SCRATCH=D + '/tmp', THREADS='1')
os.makedirs(D + '/tmp', exist_ok=True)
LOG = open(D + '/reanneal.log', 'a')

def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); LOG.write(s + '\n'); LOG.flush()

rows = []
for base in ['b33_1', 'b33_2']:
    p = f'{D}/lscreen_{base}_D10.tsv'
    if not os.path.exists(p):
        continue
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        if len(f) < 5 or not f[1].isdigit():
            continue
        costs = [int(c) for c in f[4].split(',') if c.strip().isdigit()]
        if costs:
            rows.append((min(costs), base, int(f[0]), int(f[1]), f[2]))
rows.sort()
say('screen rows with a cost:', len(rows))
for r in rows[:6]:
    say('  lowest:', r)
for cost, base, n, i, struct in rows[:2]:
    bpath = f'bases/{base}.txt'
    tab = f'{D}/tmp/tab_{base}_{n}_{i}.txt'
    pr = subprocess.run(['python3', f'{D}/prep_table.py', str(n), str(i), tab], cwd=SM, env=env,
                        capture_output=True, text=True, timeout=300)
    say('table', n, i, pr.stdout.strip(), pr.stderr.strip()[-300:])
    for seed in (2, 3):
        out = f'{D}/re_{base}_{n}_{i}_s{seed}.sol'
        t0 = time.time()
        r = subprocess.run(['nice', '-n', '10', './lanneal', tab, bpath, '10', '60', str(seed), '8', out], cwd=SM,
                           env=env, capture_output=True, text=True, timeout=200)
        res_lines = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
        if not res_lines:
            say('no RESULT line', base, n, i, seed, r.stderr[-300:]); continue
        res = res_lines[0].split()
        best = int(res[4].split('=')[1])
        volts = res[res.index('voltages') + 1:]
        say(f'REANNEAL {base} order {n} id {i} {struct} seed {seed} best={best} secs={time.time()-t0:.0f} voltages {" ".join(volts)}')
        if best == 0:
            edges = f'{D}/graph_{base}_{n}_{i}_s{seed}.edges'
            lf = subprocess.run(['python3', 'lift_edges.py', str(n), str(i), bpath, edges] + volts, cwd=SM, env=env,
                                capture_output=True, text=True, timeout=300)
            say('lift_edges rc', lf.returncode, lf.stdout.strip()[-200:], lf.stderr.strip()[-300:])
            ap = subprocess.run(['./verify/apsp', edges, '3', '10'], cwd=SM, env=env, capture_output=True, text=True,
                                timeout=600)
            say('APSP', ap.stdout.strip()[-400:], ap.stderr.strip()[-200:])
say('REANNEAL_DONE')

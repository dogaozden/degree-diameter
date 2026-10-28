#!/usr/bin/env python3
"""Calibration runs for card c13. For each (Delta, group, kind, seed) run family_score.py over primes 23..113
and record mean_excess and per-q excess. Writes results.jsonl (one line per run) in this folder."""
import json, subprocess, os, sys
HF = '/home/user/degree-diameter/research/theorems/haar_families'
CD = '/home/user/degree-diameter/research/squads/thmfam-r1/c13'
ORB = f'{HF}/gen_random_orb.py'
NOSYM = f'{CD}/gen_random_nosym.py'
done = set()
if os.path.exists(f'{CD}/results.jsonl'):
    for l in open(f'{CD}/results.jsonl'):
        r = json.loads(l); done.add((r['group'], r['Delta'], r['kind'], r['seed']))
out = open(f'{CD}/results.jsonl', 'a')
for group in ['psl', 'sl']:
    for Delta in [6, 7, 8]:
        for kind in ['sym', 'nosym']:
            for seed in range(1, 9):
                if (group, Delta, kind, seed) in done: continue  # resume support
                if kind == 'sym':
                    f = Delta - 6  # fixed letters: 0 (I absent), 1 ({I}), 2 ({I, w}); plus k=2 random 3-orbits
                    gen = f'python3 {ORB} {{q}} {f} 2 {seed}'
                else:
                    gen = f'python3 {NOSYM} {{q}} {Delta} {seed}'
                r = subprocess.run(['python3', f'{HF}/family_score.py', '--gen', gen, '--group', group,
                                    '--qrange', '23', '113', '--json'],
                                   cwd=HF, capture_output=True, text=True, timeout=1500)
                try:
                    d = json.loads(r.stdout)
                except Exception:
                    d = {'error': (r.stdout + r.stderr)[-500:]}
                rec = {'Delta': Delta, 'group': group, 'kind': kind, 'seed': seed, 'gen': gen,
                       'mean_excess': d.get('summary', {}).get('mean_excess'),
                       'rows': d.get('rows'), 'error': d.get('error')}
                out.write(json.dumps(rec) + '\n'); out.flush()
                print(Delta, group, kind, seed, rec['mean_excess'], rec['error'] and 'ERR', flush=True)

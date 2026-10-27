#!/usr/bin/env python3
"""Driver for card c2: runs cover_score.py (p=7) for each t2 rule x rk, and the random-t2 baseline (3 seeds, rk 1).
Writes results.jsonl (one line per config, with the SUMMARY) and prints a table."""
import subprocess, json, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
CS = '/home/user/degree-diameter/research/theorems/haar_families/cover_score.py'
QS = '11,13,17,19,23'; MS = '7,13,19,31,37,43,61,49,91'
sys.path.insert(0, HERE)
src = open(os.path.join(HERE, 'c2_rule.py')).read().split('def main')[0]
ns = {'__file__': os.path.join(HERE, 'c2_rule.py')}; exec(src, ns); names = list(ns['T2'])
configs = [(str(n), rk) for n in range(len(names)) for rk in (1, 2)] + [(f'rand:{s}', 1) for s in (1, 2, 3)]
out = open(os.path.join(HERE, 'results.jsonl'), 'w')
for rule, rk in configs:
    gen = f"python3 {HERE}/c2_rule.py {{p}} {{q}} {{m}} {rule} {rk}"
    cmd = ['nice', '-n', '10', 'timeout', '900', sys.executable, CS, '--p', '7', '--rule', 'cyc',
           '--qs', QS, '--ms', MS, '--gen', gen, '--maxv', '1e7']
    r = subprocess.run(cmd, capture_output=True, text=True)
    summ = None
    for line in r.stdout.splitlines():
        if line.startswith('SUMMARY '): summ = json.loads(line[8:])
    name = names[int(rule)] if rule.isdigit() else rule
    rec = {'rule': name, 'idx': rule if rule.isdigit() else None, 'rk': rk, 'summary': summ,
           'rows': [l for l in r.stdout.splitlines() if l.startswith('{')], 'rc': r.returncode, 'err': r.stderr[-300:]}
    out.write(json.dumps(rec) + '\n'); out.flush()
    print(name, rk, summ and summ['mean_excess'], summ and summ['n_full'], flush=True)

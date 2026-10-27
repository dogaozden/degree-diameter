#!/usr/bin/env python3
"""Card c1 driver: scores every label rule (arith + 16 cyc rules, each --rk 1 and 2) and the random baseline (3 seeds)
over the FULL grid with cover_score.py.  Writes results.json and prints one line per configuration."""
import subprocess, json, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = '/home/user/degree-diameter/research/theorems/haar_families'
QS = '13,17,19,23,29'
MS = '7,13,19,31,37,43,61,49,91'
RULES = ['2', 'm-1', 'm-2', 'r+1', 'r-1', '2r', 'half', 'r2+2', '3', '5', '4', 'r2', '2r+1', 'half+', 'r+2', '3r']
configs = []
for rk in (1, 2):
    configs.append((f'arith rk{rk}', ['--rule', 'arith', '--rk', str(rk)]))
    for nm in RULES:
        gen = f'python3 {HERE}/rule_gen.py {{p}} {{q}} {{m}} {nm} --rk {rk}'
        configs.append((f'cyc t2={nm} rk{rk}', ['--gen', gen]))
for s in (1, 2, 3):
    for rk in (1,):
        gen = f'python3 {HERE}/rule_gen.py {{p}} {{q}} {{m}} rand --rk {rk} --seed {s}'
        configs.append((f'BASELINE rand seed{s} rk{rk}', ['--gen', gen]))
res = []
for label, extra in configs:
    cmd = ['nice', '-n', '10', 'timeout', '900', sys.executable, f'{TOOLS}/cover_score.py', '--p', '5',
           '--qs', QS, '--ms', MS, '--maxv', '1e7'] + extra
    out = subprocess.run(cmd, capture_output=True, text=True)
    line = [l for l in out.stdout.splitlines() if l.startswith('SUMMARY ')]
    if not line:
        res.append({'label': label, 'error': out.stderr[-300:]}); print(label, 'ERROR'); continue
    s = json.loads(line[0][len('SUMMARY '):])
    s['label'] = label
    res.append(s)
    b = s['best']
    print(f"{label:32s} mean_excess={s['mean_excess']} n_full={s['n_full']}/{s['n_rows']} "
          f"vs8={b.get('8',{}).get('vs_table')} vs9={b.get('9',{}).get('vs_table')} vs10={b.get('10',{}).get('vs_table')}",
          flush=True)
json.dump(res, open(f'{HERE}/results.json', 'w'), indent=1)

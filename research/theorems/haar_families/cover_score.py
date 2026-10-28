#!/usr/bin/env python3
"""Score a label rule for LPS x Z_m covers over a grid of (q, m).
For each (q, m): build the generator lines (default: gen_lps_cover.py p q m RULE...), run haar_ecc pgl q m, record the
diameter of the component of (I,0,A) and excess = diam - log_p(|PSL(2,q)| * m) (|PSL| * m = one side of the component).
Usage: cover_score.py --p 5 --rule "arith" --qs 13,17,19,23 --ms 7,13,19,31 [--gen "CMD with {p} {q} {m}"] [--maxv 1e7]
Prints one row per (q, m) and a SUMMARY: mean excess, best vertex count per diameter D and its ratio to the 2013 table."""
import argparse, subprocess, math, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from family_score import TABLE, OURS
ap = argparse.ArgumentParser()
ap.add_argument('--p', type=int, required=True); ap.add_argument('--rule', default='arith')
ap.add_argument('--qs', required=True); ap.add_argument('--ms', required=True)
ap.add_argument('--gen'); ap.add_argument('--maxv', type=float, default=1e7); ap.add_argument('--rk', type=int, default=1)
a = ap.parse_args()
rows = []; best = {}
for q in map(int, a.qs.split(',')):
    for m in map(int, a.ms.split(',')):
        V = q * (q * q - 1) * m
        if V > a.maxv: continue
        cmd = (a.gen.format(p=a.p, q=q, m=m) if a.gen else
               f"python3 {HERE}/gen_lps_cover.py {a.p} {q} {m} {a.rule} --rk {a.rk}")
        g = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        if g.returncode: rows.append({'q': q, 'm': m, 'error': g.stderr[-200:]}); continue
        r = subprocess.run([f"{HERE}/haar_ecc", 'pgl', str(q), str(m)], input=g.stdout, capture_output=True, text=True)
        mm = re.search(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+)', r.stdout)
        if not mm: rows.append({'q': q, 'm': m, 'error': r.stdout[-200:]}); continue
        d, eA, eB, cA, cB = map(int, mm.groups())
        full = (cA == V and cB == V)
        diam = max(eA, eB)
        ex = diam - math.log(V / 2) / math.log(a.p)
        rows.append({'q': q, 'm': m, 'vertices': cA, 'full': full, 'diam': diam, 'excess': round(ex, 3)})
        if full:
            for D in range(diam, 13):
                if cA > best.get(D, (0,))[0]: best[D] = (cA, q, m)
ok = [r for r in rows if r.get('full')]
mean = sum(r['excess'] for r in ok) / len(ok) if ok else None
Delta = a.p + 1
summ = {'mean_excess': round(mean, 3) if mean is not None else None, 'n_full': len(ok), 'n_rows': len(rows),
        'best': {D: {'vertices': v, 'q': q, 'm': m, 'vs_table': round(v / TABLE[(Delta, D)], 3) if (Delta, D) in TABLE else None}
                 for D, (v, q, m) in sorted(best.items()) if 7 <= D <= 12}}
for r in rows: print(r)
print('SUMMARY', json.dumps(summ))

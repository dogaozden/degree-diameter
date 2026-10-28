#!/usr/bin/env python3
"""Summarise results.jsonl: rank configs by mean excess over FULL cells; baseline = random t2 (rk 1, 3 seeds)."""
import json, os, statistics
HERE = os.path.dirname(os.path.abspath(__file__))
recs = [json.loads(l) for l in open(os.path.join(HERE, 'results.jsonl'))]
rules = [r for r in recs if not r['rule'].startswith('rand:')]
base = [r for r in recs if r['rule'].startswith('rand:')]
def vt(r, D):
    b = r['summary']['best'].get(str(D)); return b['vs_table'] if b else None
rules.sort(key=lambda r: r['summary']['mean_excess'])
print(f"{'rule':10s} rk  mean_excess n_full  vs_table D8  D9    D10")
for r in rules:
    s = r['summary']
    print(f"{r['rule']:10s} {r['rk']}  {s['mean_excess']:.3f}      {s['n_full']:3d}  {vt(r,8)} {vt(r,9)} {vt(r,10)}")
print('BASELINE (random t2, rk 1)')
for r in base:
    s = r['summary']; print(f"{r['rule']:10s} 1  {s['mean_excess']:.3f}      {s['n_full']:3d}  {vt(r,8)} {vt(r,9)} {vt(r,10)}")
bm = [r['summary']['mean_excess'] for r in base]
print('baseline mean over seeds', round(statistics.mean(bm), 3), 'sd', round(statistics.pstdev(bm), 3))
best = rules[0]
print('BEST', best['rule'], best['rk'], best['summary']['mean_excess'])
print('best per-D', {D: (best['summary']['best'].get(str(D)) or {}).get('vertices') for D in (8, 9, 10)})

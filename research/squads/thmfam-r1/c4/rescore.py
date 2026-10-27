#!/usr/bin/env python3
"""Rescore the top K candidates of a screen file on more primes. Usage: rescore.py in.jsonl K q1,q2,.. out.jsonl"""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c4')
from screen import excess
inp, K, qs, out = sys.argv[1], int(sys.argv[2]), [int(x) for x in sys.argv[3].split(',')], sys.argv[4]
rows = [json.loads(l) for l in open(inp)]
rows.sort(key=lambda r: r['mean'])
top = rows[:K]
res = []
for r in top:
    X, Y, u, rc = tuple(r['X']), tuple(r['Y']), r['u'], r['r']
    ex = [excess(q, r['m'], X, Y, u, rc) for q in qs]
    if any(e is None for e in ex): continue
    res.append({'m': r['m'], 'X': X, 'Y': Y, 'u': u, 'r': rc, 'qs': qs, 'mean': sum(ex)/len(ex), 'ex': ex, 'q23': r['mean']})
res.sort(key=lambda r: r['mean'])
with open(out, 'w') as f:
    for r in res: f.write(json.dumps(r) + '\n')
for r in res[:5]: print(round(r['mean'], 3), [round(x, 3) for x in r['ex']], r['X'], r['Y'], r['u'], r['r'])

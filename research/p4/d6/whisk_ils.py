"""Whisker packing on H(5) as a max independent set (conflict = share a free off-S point), solved by
research/gh6/ils_mis.c. Usage: python3 whisk_ils.py SECONDS SEED"""
import json, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from delorme_q5 import setup
P, lines, N, S, through, adj = setup()
Sset = set(S); v = S[0]
onS = set(p for s in S for p in lines[s])
vlines = set(k for p in lines[v] for k in through[p])
blocked = set(p for k in vlines for p in lines[k]) - onS
cand = [k for k in range(len(lines)) if k not in Sset and k not in vlines and not any(p in blocked for p in lines[k])]
at = {}
for j, k in enumerate(cand):
    for p in lines[k]:
        if p not in onS:
            at.setdefault(p, []).append(j)
E = set()
for js in at.values():
    for a in js:
        for b in js:
            if a < b:
                E.add((a, b))
g = HERE / 'runs' / 'whisk_conflict.txt'
g.write_text(f'{len(cand)} {len(E)}\n' + ''.join(f'{a} {b}\n' for a, b in sorted(E)))
r = subprocess.run([str(HERE / 'ils_mis'), str(g), sys.argv[1], sys.argv[2]], capture_output=True, text=True)
out = r.stdout.split('\n')
sel = [cand[int(x)] for x in out[1].split()]
print('ILS whiskers', len(sel))
(HERE / 'runs' / f'whiskers_q5_ils{len(sel)}.json').write_text(json.dumps({'whiskers': sel}))

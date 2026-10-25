#!/usr/bin/env python3
"""rank.py (card c4): ranked table of the level-skeleton scan from screen_q5.tsv and confirm_q7.tsv."""
import csv, os
HERE = os.path.dirname(os.path.abspath(__file__))
rows = [r for r in csv.reader(open(os.path.join(HERE, 'screen_q5.tsv')), delimiter='\t') if r]
conf = {}
p7 = os.path.join(HERE, 'confirm_q7.tsv')
if os.path.exists(p7):
    for r in csv.reader(open(p7), delimiter='\t'):
        if r:
            conf[(r[0], r[1], r[2], r[3])] = r
passing = [r for r in rows if r[7] == 'PASS']
passing.sort(key=lambda r: (-int(r[4]), int(r[0]), int(r[1]), int(r[2]), r[3]))
out = []
out.append('# c4: level-skeleton scan (Z_L x Z_k -> Z_{Lk}, H(q) + 2 extra edges)\n')
out.append('Screen: exact check at q = 5 (lscan, all sources, 2 seeds per k, downward k-scan from the largest coprime k with '
           'L*k <= 64). Structure = (L, s1, s2, phi-mode); s1 <= s2 is one representative per unit-orbit of Z_L. '
           'Hexagon flags level 0 with random sub-voltages.\n')
out.append(f'Structures screened: {len(rows)}; with a passing design at q = 5: {len(passing)}.\n')
out.append('## Ranked (largest exact m at q = 5 first)\n')
out.append('| rank | L | (s1,s2) | phi | m at q=5 | k | seed | q=7 check (r:200 then all) |')
out.append('|---:|---:|:---:|:---|---:|---:|---:|:---|')
for i, r in enumerate(passing, 1):
    key = (r[0], r[1], r[2], r[3])
    if key in conf:
        c = conf[key]
        q7 = 'null (no k passes)' if c[4] == 'null' else f'PASS exact, m = {c[4]} (k={c[5]}, seed={c[6]})'
    else:
        q7 = 'not run'
    out.append(f'| {i} | {r[0]} | ({r[1]},{r[2]}) | {r[3]} | {r[4]} | {r[5]} | {r[6]} | {q7} |')
out.append('\n## Best m per level group L (q = 5)\n')
out.append('| L | best m | structures reaching it |')
out.append('|---:|---:|:---|')
for L in sorted({int(r[0]) for r in rows}):
    rs = [r for r in passing if int(r[0]) == L]
    if not rs:
        out.append(f'| {L} | none | - |')
        continue
    best = max(int(r[4]) for r in rs)
    who = ', '.join(f'({r[1]},{r[2]}) {r[3]}' for r in rs if int(r[4]) == best)
    out.append(f'| {L} | {best} | {who} |')
out.append('\n## Structures with no passing design (q = 5)\n')
fails = [f'L={r[0]} ({r[1]},{r[2]}) {r[3]}' for r in rows if r[7] != 'PASS']
out.append(', '.join(fails) if fails else 'none')
open(os.path.join(HERE, 'ranked.md'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out[:12]))

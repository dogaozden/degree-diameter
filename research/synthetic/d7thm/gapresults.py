#!/usr/bin/env python3
"""Turn hgrun.out into the sentence of D7_THEOREMS.md Section 4 (computer-checked hub graphs below q_k)."""
import re
ok, bad = [], []
for line in open('hgrun.out'):
    mm = re.match(r'q=(\d+) k=(\d+) d=(\d+) K_B=(\d+) K_A=(\d+): ([^:]*):', line)
    if not mm:
        continue
    q, k, d, KB, KA = map(int, mm.groups()[:5])
    how = mm.group(6)
    if 'RESULT VALID HG(%d,%d;' % (KB, KA) in line:
        ok.append('$(%d,%d)$: $\\mathrm{HG}(%d,%d;%d)$ (%s)' % (q, k, KB, KA, d, how.replace(' | haar K_A on both sides', '')))
    else:
        far = re.findall(r'far_same_colour_pairs=(\d+)', line)
        bad.append('$(%d,%d)$ (%s far pairs at best)' % (q, k, format(min(map(int, far)), ',') if far else '?'))
print('VALID: ' + '; '.join(ok) + '.')
print('NOT FOUND: ' + ', '.join(bad) + '.')

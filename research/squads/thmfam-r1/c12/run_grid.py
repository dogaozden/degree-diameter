#!/usr/bin/env python3
"""Grid over kind x norb x seed x q (q >= 29). Writes results.tsv: kind norb seed q Delta connected diam order ratio."""
import subprocess, re, sys
D = '/home/user/degree-diameter/research/squads/thmfam-r1/c12'
H = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
def W(Delta, Dm):
    return sum((Delta-1)**j for j in range(Dm))
qs = [29, 31, 37, 41, 43, 47, 53, 59, 61]
out = open(f'{D}/results.tsv', 'w')
out.write('kind\tnorb\tseed\tq\tDelta\tconnected\tdiam\torder\tratio\n')
for kind in ['split', 'nonsplit']:
  for norb in [1, 2, 3]:
    for seed in [1, 2, 3, 4]:
      for q in qs:
        g = subprocess.run(['python3', f'{D}/gen_torus.py', str(q), kind, str(norb), str(seed)],
                           capture_output=True, text=True)
        Delta = int(re.search(r'Delta=(\d+)', g.stderr).group(1))
        h = subprocess.run(['nice', '-n', '10', 'timeout', '900', H, 'psl', str(q), '1'],
                           input=g.stdout, capture_output=True, text=True)
        m = re.search(r'order=(\d+) connected=(\w+) diam=(\d+)', h.stdout)
        order, conn, diam = int(m.group(1)), m.group(2), int(m.group(3))
        G = order // 2
        ratio = G / W(Delta, diam) if conn == 'yes' else 0.0
        out.write(f'{kind}\t{norb}\t{seed}\t{q}\t{Delta}\t{conn}\t{diam}\t{order}\t{ratio:.6f}\n'); out.flush()
out.close()
print('done')

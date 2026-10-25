import sys
sys.argv = ['x']
import numpy as np
import c5_stats as c
path = '/home/user/degree-diameter/research/theorems/d8/q2/q2_j2_M44.txt'
L = c.load_file(path)
N, q, j, M1, M2 = L['N'], L['q'], L['j'], L['M1'], L['M2']
grp = c.Grp(M1, M2)
Pf, Lf, Wf, HL, HW = c.structure(L['rows'], N, L['F'], j, grp)
Wg, Tg = c.gauge(N, Pf, Lf, Wf, HL, HW, grp)
print('zero flags after gauge:', int((Wg == 0).sum()), 'of', len(Wg), '; spanning tree needs', 2 * N - 1)
rows = []
for p, l, w in zip(Pf, Lf, Wg):
    rows.append((p, N + l, w // M2, w % M2))
for hl, T in zip(HL, Tg):
    for p in range(N):
        t = T[p]
        rows.append((p, N + hl[p], t // M2, t % M2))
out = '/home/user/degree-diameter/research/squads/r3-d8/c5/gauged_q2_j2_M44.txt'
with open(out, 'w') as fh:
    fh.write(f'{2 * N} {M1} {M2} {len(rows)}\n')
    for r in rows:
        fh.write('%d %d %d %d\n' % tuple(int(x) for x in r))
print('wrote', out, len(rows))

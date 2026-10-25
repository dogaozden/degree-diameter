#!/usr/bin/env python3
"""Baseline 8 flags as 24 classes (make_cls.py full) plus E extra class-1 classes at the points listed in EXTRA
(lines "p 1"). Extra hubs use the spare slots of the unused j=2 and j=3 hubs of the baseline:
  Z_new_i ~ W_{3a+1} for a in 0..7   (spare W's of class j=2 take 8 new line-side hubs each)
  W_new_i ~ Z_{3a+2} for a in 0..7   (spare Z's of class j=3 take 8 new point-side hubs each)
Usage: make_x.py SRC.sol EXTRA.txt OUT.cls   (needs exactly 8 extra classes)"""
import sys, subprocess
src, extra, out = sys.argv[1], sys.argv[2], sys.argv[3]
ex = [tuple(map(int, l.split())) for l in open(extra) if l.strip()]
assert len(ex) == 8
N = 177156
lines = open(src).read().split('\n')
hdr = lines[0].split(); K = int(hdr[3])
freed = [int(x) for x in lines[1].split()[1:]]
hub = lines[2].split(); m = int(hub[1])
pairs = [(int(hub[2 + 2 * i]), int(hub[3 + 2 * i])) for i in range(m)]
M = ' '.join(lines[3:]).split()
classes = [(freed[a], j) for a in range(K) for j in (1, 2, 3)] + ex
T = len(classes)
hp = [(3 * a, 3 * b) for (a, b) in pairs]
base_T = 3 * K
for i in range(len(ex)):
    zi, wi = base_T + i, base_T + i
    for a in range(K):
        hp.append((zi, 3 * a + 1))      # Z_new_i ~ W of class (a, j=2)
        hp.append((3 * a + 2, wi))      # Z of class (a, j=3) ~ W_new_i
with open(out, 'w') as f:
    f.write('d7cls 11 %d %d %d\n' % (N, T, 2 * 7 * N + 2 * T))
    for p, j in classes: f.write('%d %d\n' % (p, j))
    f.write('hubedges %d\n' % len(hp))
    for t, s in hp: f.write('%d %d\n' % (t, s))
    for i in range(0, N, 16): f.write(' '.join(M[i:i + 16]) + '\n')
print('wrote', out, 'classes', T, 'hub pairs', len(hp))

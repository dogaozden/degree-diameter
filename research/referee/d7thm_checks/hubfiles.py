#!/usr/bin/env python3
"""Convert the hub graphs stored in the lab's files to edge lists for bfsd.c:
  sol <file.sol> <out>: the 'hubgraph M' block of a typed_build.py solution file (the (18,7) H(7)+H(7) graph);
  psl <hub_psl29.txt> <out>: first line K, then edges 'b a' (the (15,7) PSL(2,29) Haar hub graph of job conics)."""
import sys
mode, fn, out = sys.argv[1:4]
L = open(fn).read().split('\n')
if mode == 'sol':
    i = [j for j, l in enumerate(L) if l.startswith('hubgraph')][0]; m = int(L[i].split()[1])
    K1, K2 = map(int, [l for l in L if l.startswith('hubs ')][0].split()[1:3])
    E = [tuple(map(int, L[i + 1 + t].split())) for t in range(m)]
else:
    K1 = K2 = int(L[0]); E = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
assert all(0 <= a < K1 and 0 <= b < K2 for a, b in E)
with open(out, 'w') as f:
    f.write('%d %d\n' % (K1 + K2, len(E)))
    for a, b in E: f.write('%d %d\n' % (a, K1 + b))
print('%s: %d + %d hubs, %d edges -> %s' % (fn.split('/')[-1], K1, K2, len(E), out))

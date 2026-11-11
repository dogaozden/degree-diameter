#!/usr/bin/env python3
"""build.py BASE.edges OUT.edges PREFIX  : G + hubs from PREFIX_A.txt, PREFIX_B.txt (old neighbours, global ids)
plus hub-hub edges from PREFIX_HH.txt (lines 'a b': index of A-hub line a, index of B-hub line b)."""
import sys
base, out, pre = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(base).read().split('\n')
n = int(lines[0]); E = [l for l in lines[1:] if l.strip()]
A = [list(map(int, l.split())) for l in open(pre + '_A.txt') if l.strip()]
B = [list(map(int, l.split())) for l in open(pre + '_B.txt') if l.strip()]
HH = [tuple(map(int, l.split())) for l in open(pre + '_HH.txt') if l.strip()]
used = set(); k = n; idA = []; idB = []
for nb in A:
    idA.append(k); k += 1
    for x in nb: assert x not in used; used.add(x); E.append(f"{idA[-1]} {x}")
for nb in B:
    idB.append(k); k += 1
    for x in nb: assert x not in used; used.add(x); E.append(f"{idB[-1]} {x}")
for a, b in HH: E.append(f"{idA[a]} {idB[b]}")
with open(out, 'w') as f:
    f.write(f"{k}\n"); f.write('\n'.join(E) + '\n')
print('hubs A', len(A), 'B', len(B), 'hub-hub', len(HH), 'n', k)

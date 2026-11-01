#!/usr/bin/env python3
"""merge_hubs.py BASE.edges OUT.edges HUBFILE [HUBFILE ...]: append one new vertex per hub line (old neighbour ids)."""
import sys
base, out, hubfiles = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(base).read().split('\n')
n = int(lines[0]); E = [l for l in lines[1:] if l.strip()]
used = set(); k = n
for hf in hubfiles:
    for l in open(hf):
        nb = list(map(int, l.split()))
        if not nb: continue
        for x in nb:
            assert x not in used, ('old vertex used twice', x); used.add(x); E.append(f"{k} {x}")
        k += 1
with open(out, 'w') as f:
    f.write(f"{k}\n"); f.write('\n'.join(E) + '\n')
print('vertices', k, 'hubs', k - n, 'edges', len(E))

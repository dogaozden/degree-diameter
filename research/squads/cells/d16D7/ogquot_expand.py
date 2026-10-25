#!/usr/bin/env python3
"""ogquot_expand.py MAP QSOL OUT: expand a quotient solution (quotient vertex ids, one per line) to orbit-graph vertex
indices using the MAP file written by ogquot.py. Check the result with ogscore.py."""
import sys
mp = [list(map(int, l.split())) for l in open(sys.argv[1])]
out = []
for l in open(sys.argv[2]):
    l = l.strip()
    if l and not l.startswith('#'):
        out += mp[int(l)]
open(sys.argv[3], 'w').write('\n'.join(map(str, sorted(out))) + '\n')
print(len(out), 'orbit-graph vertices')

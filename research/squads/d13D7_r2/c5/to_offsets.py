#!/usr/bin/env python3
"""Convert a clique (vertices (s,b,c,f) of G, one per line, '#' lines ignored) into fiblift offsets 'a b c e f'
with a=0, b, c, e=s, f, after translating so that the clique contains 0 = (0,0,0,0).
usage: to_offsets.py VERTS OFFSETS_OUT"""
import sys
import numpy as np
rows = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
V = np.array(rows, dtype=np.int64) % 11
V = (V - V[0]) % 11          # translate: first vertex becomes 0
seen = set(map(tuple, V.tolist()))
assert len(seen) == len(V), 'duplicate vertices'
with open(sys.argv[2], 'w') as f:
    f.write(f'# {len(V)} offsets (a b c e f) with a=0, e=s; translated so that 0 is in the clique\n')
    for s, b, c, fx in V.tolist():
        f.write(f'0 {b} {c} {s} {fx}\n')
print(len(V), 'offsets written to', sys.argv[2])

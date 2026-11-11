#!/usr/bin/env python3
"""Swap the two matrix factors of a 'prod' sol file (research/frontier/sols format). The Haar graph of G1 x G2 x Z_n
with connection set S is isomorphic to that of G2 x G1 x Z_n with the swapped S, so the swapped file describes the
same graph; lean-all puts the larger PSL factor first (fewer, larger batches).

usage: swap_sol.py IN OUT"""
import re, sys

lines = open(sys.argv[1]).read().split('\n')
h = lines[0].split()
assert h[2] == 'prod' and h[7] == 'n', 'prod sl|psl p sl|psl q n n ... only'
h[3], h[4], h[5], h[6] = h[5], h[6], h[3], h[4]
out = [' '.join(h)]
for l in lines[1:]:
    m = re.match(r'(\s*\d+\s+)prod\[(mat\([^)]*\));(mat\([^)]*\))\](.*)', l)
    out.append(f'{m.group(1)}prod[{m.group(3)};{m.group(2)}]{m.group(4)}' if m else l)
open(sys.argv[2], 'w').write('\n'.join(out))

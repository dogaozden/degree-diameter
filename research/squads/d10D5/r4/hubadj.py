#!/usr/bin/env python3
"""hubadj.py X.sol "FDSET": HUBADJ string (flag pairs i:j of enabled hub edges, H=3 numbering) for dmfast_fd."""
import sys
rows = {}
for ln in open(sys.argv[1]):
    t = ln.split()
    if t: rows[t[0]] = t[1:]
FD = set(int(x) for x in sys.argv[2].split()); hg = [int(x) for x in rows['hubgraph']]
on = lambda h: h % 3 < 2 or h // 3 in FD
print(' '.join(sorted(set('%d:%d' % (hg[e] // 3, hg[e + 1] // 3) for e in range(0, len(hg), 2) if on(hg[e]) and on(hg[e + 1])))))

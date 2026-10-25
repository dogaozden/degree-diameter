#!/usr/bin/env python3
"""convert.py TAG IDS OUT: expands a list of orbit vertex ids (as written by kts) into the line ids of those orbits."""
import sys, numpy as np
C3 = '/home/user/degree-diameter/research/squads/c157b-r1/c3/'
tag, idsf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
raw = np.fromfile(C3 + 'members_%s.bin' % tag, dtype=np.int32)
s, nv = int(raw[0]), int(raw[1])
mem = raw[2:].reshape(nv, s)
v = np.loadtxt(idsf, dtype=np.int64).reshape(-1)
lines = np.sort(mem[v].reshape(-1))
np.savetxt(outf, lines, fmt='%d')
print('orbits', len(v), 'lines', len(lines))

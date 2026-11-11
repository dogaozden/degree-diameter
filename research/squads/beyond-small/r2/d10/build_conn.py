#!/usr/bin/env python3
"""build_conn.py BASE.edges HUBS GROUPS OUT.edges: append hubs (one vertex per HUBS line: old neighbour ids) and
connectors (one vertex per GROUPS line: hub line indices, joined to those hubs)."""
import sys
base, hubf, grpf, out = sys.argv[1:5]
lines = open(base).read().split('\n')
n = int(lines[0]); E = [l for l in lines[1:] if l.strip()]
hubs = [list(map(int, l.split())) for l in open(hubf) if l.strip()]
used = set(); k = n; hubid = []
for nb in hubs:
    hubid.append(k)
    for x in nb:
        assert x not in used, ('old vertex used twice', x); used.add(x); E.append(f"{k} {x}")
    k += 1
nconn = 0
for l in open(grpf):
    if not l.strip(): continue
    idx = list(map(int, l.split()))
    for a in idx: E.append(f"{k} {hubid[a]}")
    k += 1; nconn += 1
with open(out, 'w') as f:
    f.write(f"{k}\n"); f.write('\n'.join(E) + '\n')
print('vertices', k, 'hubs', len(hubs), 'connectors', nconn, 'edges', len(E))

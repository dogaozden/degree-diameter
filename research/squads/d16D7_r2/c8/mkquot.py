# quotient conflict graphs under h: vertices = valid generic line-orbit rows (spread) / point-orbit rows (dual)
# two rows conflict iff they share a column. Writes og-format graphs (M E, idx rep deg nbrs) with rep = row id.
import numpy as np, sys, pickle
from collections import defaultdict
kind = sys.argv[1]      # 'sp' or 'pt'
inst = open('hexact_spread.txt' if kind == 'sp' else 'hexact_dual.txt').read().split('\n')
hdr = inst[0].split(); rows = []
for line in inst[1:]:
    if not line.strip(): continue
    a = list(map(int, line.split()))
    rows.append((a[0], a[1:]))
# keep generic rows only (size 14)
gen = [(rid, cols) for rid, cols in rows if len(cols) == 14]
ncol = int(hdr[1])
colrows = defaultdict(list)
for i, (rid, cols) in enumerate(gen):
    for c in cols: colrows[c].append(i)
nb = [set() for _ in gen]
for c, lst in colrows.items():
    for a in lst:
        for b in lst:
            if a != b: nb[a].add(b)
E = sum(len(s) for s in nb) // 2
with open(f'quot_{kind}.txt', 'w') as f:
    f.write(f'{len(gen)} {E}\n')
    for i, (rid, cols) in enumerate(gen):
        s = sorted(nb[i])
        f.write(f'{i} {rid} {len(s)} ' + ' '.join(map(str, s)) + '\n')
pickle.dump([rid for rid, _ in gen], open(f'quot_{kind}_rid.pkl', 'wb'))
print(kind, 'generic rows', len(gen), 'edges', E, 'avg deg', 2*E/len(gen), 'columns', ncol)

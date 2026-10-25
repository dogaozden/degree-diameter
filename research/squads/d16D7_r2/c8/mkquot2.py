# generic (183-element) h-orbit rows only; weight 3 in g-orbit units. Hub/inside rows (61) are kept aside.
import numpy as np, sys, pickle
from collections import defaultdict
kind = sys.argv[1]
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
orbs = meta['orbs_l'] if kind == 'sp' else meta['orbs_p']
inst = open('hexact_spread.txt' if kind == 'sp' else 'hexact_dual.txt').read().split('\n')
hdr = inst[0].split(); rows = []
for line in inst[1:]:
    if not line.strip(): continue
    a = list(map(int, line.split())); rows.append((a[0], a[1:]))
gen = [(rid, cols) for rid, cols in rows if len(orbs[rid]) == 183]
aside = [(rid, cols) for rid, cols in rows if len(orbs[rid]) != 183]
print(kind, 'valid rows', len(rows), 'generic(183)', len(gen), 'aside(61)', [(rid, len(cols)) for rid, cols in aside])
colrows = defaultdict(list)
for i, (rid, cols) in enumerate(gen):
    for c in cols: colrows[c].append(i)
nb = [set() for _ in gen]
for c, lst in colrows.items():
    for a in lst:
        for b in lst:
            if a != b: nb[a].add(b)
E = sum(len(s) for s in nb) // 2
with open(f'quot2_{kind}.txt', 'w') as f:
    f.write(f'{len(gen)} {E}\n')
    for i, (rid, cols) in enumerate(gen):
        s = sorted(nb[i])
        f.write(f'{i} {rid} {len(s)} ' + ' '.join(map(str, s)) + '\n')
pickle.dump({'rid': [rid for rid, _ in gen], 'aside': aside}, open(f'quot2_{kind}_map.pkl', 'wb'))
print(kind, 'edges', E, 'avg deg', round(2*E/len(gen), 1), 'columns', len(colrows))

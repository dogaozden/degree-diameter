# super-row instances: rows = sigma-orbits of valid h-rows (union of columns must be disjoint)
import numpy as np, sys, pickle
from collections import defaultdict
kind = sys.argv[1]
inst = open('hexact_spread.txt' if kind == 'sp' else 'hexact_dual.txt').read().split('\n')
hdr = inst[0].split()
rows = {}
for line in inst[1:]:
    if not line.strip(): continue
    a = list(map(int, line.split())); rows[a[0]] = a[1:]
smap = np.load('sl_map.npy' if kind == 'sp' else 'sp_map.npy')
ncol = int(hdr[1])
seen = set(); supers = []
for r in sorted(rows):
    if r in seen: continue
    orb = [r]; x = int(smap[r])
    while x != r:
        orb.append(x); x = int(smap[x])
    for y in orb: seen.add(y)
    if any(y not in rows for y in orb):
        continue  # should not happen (validity is sigma-invariant)
    cols = []
    for y in orb: cols += rows[y]
    if len(set(cols)) != len(cols):
        continue  # members overlap: no sigma-invariant packing can use this orbit
    supers.append((tuple(orb), cols))
print(kind, 'super-rows', len(supers), 'sizes', Counter := None)
from collections import Counter
print(Counter(len(c) for _, c in supers), 'orbit lengths', Counter(len(o) for o, _ in supers))
pickle.dump(supers, open(f'super_{kind}.pkl', 'wb'))
with open(f'super_{kind}.txt', 'w') as f:
    f.write(f'{len(supers)} {ncol}\n')
    for i, (orb, cols) in enumerate(supers):
        f.write(f'{i} ' + ' '.join(map(str, cols)) + '\n')

import pickle, sys
kind = sys.argv[1]
supers = pickle.load(open(f'super_{kind}.pkl', 'rb'))
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
orbs = meta['orbs_l'] if kind == 'sp' else meta['orbs_p']
from collections import defaultdict
W = [sum(len(orbs[r]) for r in orb) // 61 for orb, _ in supers]
bycol = defaultdict(list)
for i, (_, cols) in enumerate(supers):
    for c in cols: bycol[c].append(i)
nb = [set() for _ in supers]
for c, lst in bycol.items():
    for a in lst:
        for b in lst:
            if a != b: nb[a].add(b)
with open(f'wg_{kind}.txt', 'w') as f:
    f.write(f'{len(supers)}\n')
    for i in range(len(supers)):
        s = sorted(nb[i])
        f.write(f'{W[i]} {len(s)} ' + ' '.join(map(str, s)) + '\n')
print(kind, 'vertices', len(supers), 'avg deg', sum(len(s) for s in nb)/len(nb))

# Exact covers invariant under h (order 183): spreads (rows = h-line-orbits) and dual (rows = h-point-orbits).
import numpy as np, sys
from collections import Counter, defaultdict
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import build_PL, orbits_of
q, N, L, LP, X = load_hex()
hp = load_perm(D+'data/g13o183_pts.bin'); hl = load_perm(D+'data/g13o183_lines.bin')
PL = build_PL(LP, N)
op, orbs_p = orbits_of(hp); ol, orbs_l = orbits_of(hl)
NP, NL = len(orbs_p), len(orbs_l)
print('h point orbits', NP, 'line orbits', NL, flush=True)
np.save('hop.npy', op); np.save('hol.npy', ol)
# spreads: rows = line orbits, columns = point orbits; N(O_L,O_P) = #lines of O_L through rep point of O_P
rowcols = defaultdict(lambda: defaultdict(int))
for o, cyc in enumerate(orbs_p):
    p = cyc[0]
    for l in PL[p]:
        rowcols[int(ol[l])][o] += 1
# row O_L valid iff every N = 1 (use orbit sizes check)
valid_sp = []
for lo in range(NL):
    d = rowcols.get(lo, {})
    if all(v == 1 for v in d.values()) and len(d) > 0:
        valid_sp.append(lo)
print('spread: valid line-orbit rows', len(valid_sp), 'row sizes', Counter(len(rowcols[lo]) for lo in valid_sp))
# column degrees
deg = Counter()
for lo in valid_sp:
    for o in rowcols[lo]: deg[o] += 1
print('spread: column candidate counts', Counter(deg[o] for o in range(NP)))
with open('hexact_spread.txt', 'w') as f:
    f.write(f'{len(valid_sp)} {NP}\n')
    for lo in valid_sp:
        f.write(f'{lo} ' + ' '.join(str(o) for o in sorted(rowcols[lo])) + '\n')
# dual / points: rows = point orbits, columns = line orbits, a = #points of O_P on rep line of O_L
rowl = defaultdict(lambda: defaultdict(int))
for lo, cyc in enumerate(orbs_l):
    l = cyc[0]
    for q_ in LP[l]:
        rowl[int(op[q_])][lo] += 1
valid_pt = [po for po in range(NP) if len(rowl.get(po, {})) > 0 and all(v == 1 for v in rowl[po].values())]
print('dual: valid point-orbit rows', len(valid_pt), 'row sizes', Counter(len(rowl[po]) for po in valid_pt))
degl = Counter()
for po in valid_pt:
    for lo in rowl[po]: degl[lo] += 1
print('dual: column candidate counts', Counter(degl[lo] for lo in range(NL)))
with open('hexact_dual.txt', 'w') as f:
    f.write(f'{len(valid_pt)} {NL}\n')
    for po in valid_pt:
        f.write(f'{po} ' + ' '.join(str(lo) for lo in sorted(rowl[po])) + '\n')
import pickle
pickle.dump(dict(sp=valid_sp, pt=valid_pt, orbs_p=orbs_p, orbs_l=orbs_l), open('hexact_meta.pkl', 'wb'))

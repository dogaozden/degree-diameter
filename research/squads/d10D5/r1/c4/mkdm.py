"""mkdm.py FLAGS(p:l ...) SOL0 OUTPREFIX: sigma from the perfect matching (pflag.matching) for the given freed flags,
nu from SOL0 (lift2 DM format), writes OUTPREFIX.sol (lift2 format, mv0=1, mv1=4), OUTPREFIX.sol.free, and the hub-graph
B (pflag.hub_anneal, same seed/iters as search.py) to OUTPREFIX.B (lines 'a b' = L-hub a, P-hub b)."""
import sys
sys.path.insert(0, '.')
from pflag import *
flags = [tuple(map(int, t.split(':'))) for t in sys.argv[1].split()]
sol0 = sys.argv[2]; out = sys.argv[3]
sz, mL = matching(flags)
assert sz == N, ('matching not perfect', sz)
tok = open(sol0).read().split()
nu = tok[7 + 4 * N:7 + 4 * N + N * Q1]
assert len(nu) == N * Q1
with open(out + '.sol', 'w') as f:
    f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, mL)); f.write(s + '\n' + s + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu) + '\n')
with open(out + '.sol.free', 'w') as f: f.write(' '.join(str(p) for p, l in flags) + '\n')
patch, commA, commB, coll, conc, NEED1, NEED2 = relations(flags)
cst, B = hub_anneal(len(flags), patch, commA, commB, iters=60000, seed=4)
with open(out + '.B', 'w') as f:
    for a in range(len(B)):
        for b in range(len(B)):
            if B[a][b]: f.write(f'{a} {b}\n')
print('matching', sz, 'hub requirement violations', cst, 'hub-hub edges', sum(map(sum, B)))
print('coll', [(i, j) for i in range(len(flags)) for j in range(i) if coll[i][j]], 'conc', [(i, j) for i in range(len(flags)) for j in range(i) if conc[i][j]])
print('patch', [(x, y) for x in range(len(flags)) for y in range(len(flags)) if patch[x][y]])

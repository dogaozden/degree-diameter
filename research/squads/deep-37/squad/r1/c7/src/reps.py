# usage: reps.py BASE OUT : orbit representatives of the colour-preserving automorphism group, per colour class
import sys, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-37/src')
import gutil
fn, out = sys.argv[1], sys.argv[2]
n, E, adj = gutil.load(fn)
col = gutil.sides(adj)
perms, gs, _ = gutil.aut_gens(adj)
G = gutil.group_closure(perms, n)
H = [g for g in G if all(col[g[v]] == col[v] for v in range(n))]
print('|Aut|', len(G), '|Aut_col|', len(H), 'grpsize', gs, file=sys.stderr)
orbs = gutil.orbits_of([list(h) for h in H], n)
reps = []
for o in orbs:
    reps.append(o[0])
with open(out, 'w') as f:
    for r in reps: f.write(f"{r} {col[r]} {len(orbs)}\n")
print('orbits', len(orbs), [(len(o), col[o[0]]) for o in orbs], file=sys.stderr)

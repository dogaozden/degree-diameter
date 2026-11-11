# Grow a Z_121 base from K to K+1 orbits per side: pick 16 edges (i_t,j_t,a_t) forming a matching, replace each by
# (i_t, J_new, b_t) and (I_new, j_t, c_t). Keeps every old degree at 16 and gives the two new orbits degree 16.
import random, sys
seed = int(sys.argv[2]); random.seed(seed)
lines = open(sys.argv[1]).read().split('\n')
K, M, D = map(int, lines[0].split())
E = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
# greedy random matching of 16 edges with distinct i and distinct j
random.shuffle(E); used_i, used_j, pick = set(), set(), []
for e in E:
    if e[0] not in used_i and e[1] not in used_j and len(pick) < D:
        pick.append(e); used_i.add(e[0]); used_j.add(e[1])
assert len(pick) == D
I_new, J_new = K, K
keep = [e for e in E if e not in pick]
new = []
for (i, j, a) in pick:
    new.append((i, J_new, random.randrange(M)))
    new.append((I_new, j, random.randrange(M)))
E2 = keep + new
with open(sys.argv[3], 'w') as f:
    f.write(f'{K+1} {M} {D}\n')
    for i, j, a in E2: f.write(f'{i} {j} {a}\n')
print('edges', len(E2), file=sys.stderr)

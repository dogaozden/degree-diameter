"""Hyperplane sections of H(5) in Q(6,5): find an elliptic section (Hermitian spread)."""
import json, itertools, sys
d = json.load(open('../gh6/hex/hexagon_q5.json'))
sys.path.insert(0, "../gh6"); import gh_build; q = 5; P = gh_build.quadric_points(q); L = d["lines"]; assert len(P) == d["points"]
def bil(u, v):  # polarisation of x0x4+x1x5+x2x6-x3^2
    return (u[0]*v[4]+u[4]*v[0]+u[1]*v[5]+u[5]*v[1]+u[2]*v[6]+u[6]*v[2]-2*u[3]*v[3]) % q
for u in [(0,0,0,1,0,0,0),(1,0,0,0,1,0,0),(1,0,0,0,2,0,0),(1,0,0,0,3,0,0),(1,0,0,0,4,0,0)]:
    O = {i for i, p in enumerate(P) if bil(u, p) == 0}
    inside = [j for j, l in enumerate(L) if all(p in O for p in l)]
    meet = {sum(p in O for p in l) for l in L}
    print(u, len(O), len(inside), sorted(meet))

u = (1, 0, 0, 0, 2, 0, 0)
O = {i for i, p in enumerate(P) if bil(u, p) == 0}
spread = [j for j, l in enumerate(L) if all(p in O for p in l)]
json.dump({'O': sorted(O), 'spread': spread}, open('runs/herm_q5.json', 'w'))
# collinearity graph on O^c
rest = [i for i in range(len(P)) if i not in O]
idx = {p: k for k, p in enumerate(rest)}
E = set()
for l in L:
    r = [idx[p] for p in l if p in idx]
    for a, b in itertools.combinations(sorted(r), 2):
        E.add((a, b))
sys.path.insert(0, '../../problems/bipartite_dd'); import lib
open('runs/col_Oc.graph', 'w').write(lib.graph_to_text(len(rest), sorted(E)))
json.dump(rest, open('runs/col_Oc_ids.json', 'w'))
print('O^c', len(rest), 'edges', len(E))

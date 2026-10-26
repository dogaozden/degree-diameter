"""Full automorphism group of the incidence graph of W(11) with the regular spread S's lines coloured separately.
Automorphisms of the coloured graph = collineations of W(11) (no dualities: points and lines get different colours)
that map S to S. Uses igraph (BLISS). Writes generators to autS_gens.json."""
import json, igraph as ig
S_ = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r2/c2/struct.json'))
lines, plines, S = S_['lines'], S_['plines'], set(S_['S'])
npts = len(plines); nl = len(lines)
edges = [(p, npts + l) for l in range(nl) for p in lines[l]]
g = ig.Graph(n=npts + nl, edges=edges)
color = [0] * npts + [1 if l in S else 2 for l in range(nl)]
print('vertices', g.vcount(), 'edges', g.ecount(), flush=True)
print('group size', g.count_automorphisms(color=color), flush=True)
gens = g.automorphism_group(color=color)
gp = [p[:npts] for p in gens]
assert all(sorted(p) == list(range(npts)) for p in gp)
json.dump(gp, open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/autS_gens.json', 'w'))
print('generators', len(gp), flush=True)

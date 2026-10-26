import sys, json, glob
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, is_partial_ovoid
G = W(9)
best = None
for fn in sys.argv[1:]:
    lines = open(fn).read().split()
    k = int(lines[0]); S = sorted(int(x) for x in lines[1:1+k])
    assert len(S) == k and len(set(S)) == k
    ok = is_partial_ovoid(G, S)
    print(fn, k, ok)
    if ok and (best is None or len(S) > len(best)):
        best = S
print("BEST", len(best))
json.dump(best, open('/home/user/degree-diameter/research/squads/gqd5-r1/c1/best_W9.json', 'w'))
json.dump([list(map(int, G.coords[i])) if hasattr(G.coords[i], '__iter__') else G.coords[i] for i in best],
          open('/home/user/degree-diameter/research/squads/gqd5-r1/c1/best_W9_coords.json', 'w'))

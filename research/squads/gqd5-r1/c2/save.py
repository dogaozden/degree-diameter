import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib, numpy as np
G = gqlib.W(11)
src = sys.argv[1]
S = sorted(json.load(open(src))['S'])
ok = gqlib.is_partial_ovoid(G, S)
print('size', len(S), 'valid', ok, 'distinct', len(set(S)) == len(S))
if ok:
    json.dump(S, open('/home/user/degree-diameter/research/squads/gqd5-r1/c2/best_W11.json', 'w'))
    json.dump([list(map(int, G.coords[i])) for i in S], open('/home/user/degree-diameter/research/squads/gqd5-r1/c2/best_W11_coords.json', 'w'))
    print('saved')

import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4, W
from localdual import local_duality_pair, pick_pair
from repair import exact_conditions
for G in (Q4(7), W(7)):
    x, y, l, m = pick_pair(G)
    M = local_duality_pair(G, x, y, l, m)
    t = time.time()
    print(G.name, exact_conditions(G, 'H', 'H', M, {x, y})[0], 'time %.2f' % (time.time() - t))

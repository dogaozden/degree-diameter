import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W, is_partial_ovoid, is_partial_spread
from repair import exact_conditions, brute_bad, full_dist
q = 5
Wq = W(q); G = Wq.dual('Q(4,5)')
N = G.np
OV = sorted(regular_spread_W(Wq))          # ovoid of Q(4,5) (point ids of G)
assert is_partial_ovoid(G, OV) and len(OV) == q*q+1

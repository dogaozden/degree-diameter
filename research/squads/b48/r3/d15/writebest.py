import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r3/d15')
from grp_mat import make_group
from coset import build_nbr, cost_of, write_edges
N, mul = make_group('PGL', 23)
H = (0, 1583, 10691, 11659); K = (0, 5433, 6687, 8425)
nbr, idH, idK, NL = build_nbr(N, mul, H, K)
print("cost", cost_of(nbr, NL), "n", 2*NL)
write_edges('/home/user/degree-diameter/research/squads/b48/r3/d15/best_pgl23_96.edges', nbr, NL)

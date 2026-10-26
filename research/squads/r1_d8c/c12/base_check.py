import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c12')
from lift import *
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
N, base, match, s1, s2 = make_base(q, seed)
S = 2 * N
print('q', q, 'N', N, 'S', S, 'vertices', M * S, 'deg', q + 3)
print(gcost(S, base + match, 8, f'base{q}'))

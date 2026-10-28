import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from hubgraph import *
S = [int(x) for x in np.load('spread_ls.npy')]
O = [int(x) for x in np.load('ovoid_ls.npy')]
c = 5
R0 = S + [c]
n, E, deg = build_graph(R0, O, [], [], [])
print('no hubs, R0=S+c, R2=ovoid:', evaluate(n, E, 'x'), apsp_check(n, E, 'x'))
n, E, deg = build_graph(S, O, [], [], [])
print('no hubs, R0=S, R2=ovoid:', evaluate(n, E, 'x'), apsp_check(n, E, 'x'))
n, E, deg = build_graph([], [], [], [], [])
print('base:', evaluate(n, E, 'x'), apsp_check(n, E, 'x'))

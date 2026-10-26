import sys, json; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from hubgraph import *
S = [int(x) for x in np.load('spread_ls.npy')]
O = set(int(x) for x in np.load('ovoid_ls.npy'))
def ovpt(l): return [p for p in G.lines[l] if p in O]
print('ovoid points on lines 5,3,68:', ovpt(5), ovpt(3), ovpt(68))
R0 = S + [5]
w = {l: ovpt(l)[0] for l in (5, 3, 68)}
Ah = [[('t', w[5]), ('b', 3), ('b', 68)], [('t', w[3]), ('t', w[68]), ('b', 5)]]
n, E, deg = build_graph(R0, sorted(O), [], Ah, [])
print('A-hubs only, R0=S+5, R2=ovoid:', evaluate(n, E, 'A'), apsp_check(n, E, 'A'))
# variant: only the pair (5,3) (no 68)
R0b = [x for x in R0 if x != 68]

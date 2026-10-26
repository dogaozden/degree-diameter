import sys, json; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from hubgraph import *
S = [int(x) for x in np.load('spread_ls.npy')]
O = sorted(int(x) for x in np.load('ovoid_ls.npy'))
def ovpt(l): return [p for p in G.lines[l] if p in set(O)]
R0 = S + [5]
w = {l: ovpt(l)[0] for l in (5, 3, 68)}
# single B-hub on alpha_5 and sigma_s
for name, Bh, Ah in [
    ('B{alpha5,sigma_w5}', [[('a', 5), ('s', w[5])]], []),
    ('A{tau_w5,beta_3}', [], [[('t', w[5]), ('b', 3)]]),
    ('A{tau_w5,beta_3,beta_68}', [], [[('t', w[5]), ('b', 3), ('b', 68)]]),
    ('B{alpha5,sigma_w5} + A{tau_w5,beta_3,beta68} ', [[('a', 5), ('s', w[5])]], [[('t', w[5]), ('b', 3), ('b', 68)]]),
]:
    n, E, deg = build_graph(R0, O, Bh, Ah, [])
    print(name, evaluate(n, E, 'R'), 'n', n)

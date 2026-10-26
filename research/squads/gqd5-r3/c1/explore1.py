# explore: subgroups of H1 fixing L_inf pointwise; orbits; relaxed orbits
import sys, numpy as np, collections
sys.argv = ['x', 'H1.npy']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c1')
import orbsat2 as O
H = O.H; G = O.G; n = O.n
Linf = [p for p in range(n) if O.sline[p] == O.sline[O.rep[0]]] if False else None
Linf = list(G.lines[O.S[0]])
fix = [g for g in H if all(g[p] == p for p in Linf)]
print('fixing L_inf pointwise', len(fix))
orbs = O.orbits_of(fix)
print('orbit sizes', collections.Counter(len(o) for o in orbs))
rel = [o for o in orbs if O.relaxed(o)]
print('relaxed orbits sizes', [len(o) for o in rel])
# orbits of the setwise stabiliser of L_inf (order 3240/82?) and the group acting on other S-lines
# check the cycle types: order of elements in fix
def order(g):
    k=1; c=g.copy(); idp=np.arange(n)
    while not np.array_equal(c, idp): c=g[c]; k+=1
    return k
print('orders in fix', collections.Counter(order(g) for g in fix))

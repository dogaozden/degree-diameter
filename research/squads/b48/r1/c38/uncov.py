import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import numpy as np, groups
T = groups.table('heis 11')
N = T.shape[0]
# read state
volt = [int(l.split()[3]) for l in open(sys.argv[1]) if l.startswith('e ')]
print('volt', volt)
# words: BFS over reduced non-backtracking walks in the Haar graph (side A vertex x -> side B x*s)
S = volt
inv = [int(np.where(T[g]==0)[0][0]) for g in range(N)]
gens = S + [inv[s] for s in S]
# distance from identity on lift: vertices (A,x), (B,y). A->B by right mult with s.
# compute ball via BFS on Cayley-like Haar graph: A-vertex x adjacent to B-vertex x*s, B-vertex y adjacent to A-vertex y*s^-1
distA = -np.ones(N, int); distB = -np.ones(N, int)
distA[0] = 0
frontier = [('A', 0)]
d = 0
while frontier and d < 8:
    nxt = []
    for side, x in frontier:
        if side == 'A':
            for s in S:
                y = int(T[x, s])
                if distB[y] < 0: distB[y] = d+1; nxt.append(('B', y))
        else:
            for s in S:
                y = int(T[x, inv[s]])
                if distA[y] < 0: distA[y] = d+1; nxt.append(('A', y))
    frontier = nxt; d += 1
print('uncovered A', int((distA<0).sum()), 'uncovered B', int((distB<0).sum()))
print('uncovered A list sample', np.where(distA<0)[0][:30])
# structure of uncovered B set
U = [y for y in range(N) if distB[y] < 0]
# coordinates: groups.py heis p index -> need element decomposition; find centre and abelianisation via commutators
comm = set()
e = 0
# centre: elements commuting with all
Z = [g for g in range(N) if all(T[g,h]==T[h,g] for h in range(0,N,max(1,N//60)))]
print('centre approx size', len(Z))
# order of elements
def order(g):
    k=1; x=g
    while x!=0: x=int(T[x,g]); k+=1
    return k
print('orders of uncovered sample', [order(y) for y in U[:12]])
print('uncovered count', len(U))

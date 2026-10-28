import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from hub import *
from bad import dist_matrix
for q in (3,5):
    G=getG(q); M=random_M01(G,1)
    x=0; s=G.plines[0][0]; y=[p2 for p2 in G.lines[s] if p2!=x][0]
    n,E,per,Ys=hub_edges(G,[x,y],M)
    D=dist_matrix(n,E); n0=3*per
    base=[a for a in range(n0)]
    sub=D[np.ix_(base,base)]
    print('q',q,'pair {x,y} with B-hub(y)-A-hub(x) edges: base-vertex pairs at dist>5:', int((sub>5).sum()//2), '; max base dist', int(sub.max()), '; Y edges', Ys)

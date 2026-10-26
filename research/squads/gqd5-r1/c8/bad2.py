import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from bad import *
q=3
G=getG(q); M=random_M01(G,1)
x=0; s=G.plines[0][0]; y=[p2 for p2 in G.lines[s] if p2!=x][0]
n,E,per=base_edges(G,M,[x,y])
D=dist_matrix(n,E)
bad=np.argwhere(D>5)
for a,b in bad:
    if a<b: print(label(a,per,G.np), label(b,per,G.np), 'collinear-ness of pt with line:', G.I[ a%per if a%per<G.np else b%per, (b%per if a%per<G.np else a%per)-G.np] if (a%per<G.np or b%per<G.np) else '')
print('x,y',x,y,'s',s)
print('lines through y:', G.plines[y], 'lines through x:', G.plines[x])

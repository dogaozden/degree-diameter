import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from linehub import *
from bad import dist_matrix
from collections import Counter
q=int(sys.argv[1]); G=getG(q); M=random_M01(G,int(sys.argv[2]) if len(sys.argv)>2 else 1)
S=partial_spread(G,0)
n,E,per,R=line_hub_edges(G,S,M)
D=dist_matrix(n,E); n0=3*per; nS=len(S)
def lab(v):
    if v<n0:
        j=v//per; e=v%per
        return ('L%d'%j)+('p' if e<G.np else 'l')
    k=v-n0
    return 'hB' if k<nS else 'hA'
c=Counter()
for a in range(n):
    for b in range(a+1,n):
        if D[a,b]>5: c[(lab(a),lab(b),int(D[a,b]))]+=1
print('S size',nS,'bad pair classes',c)
print('numbers of bad pairs',sum(c.values()))

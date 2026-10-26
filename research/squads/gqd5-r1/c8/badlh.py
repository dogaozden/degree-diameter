import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from linehub import *
from bad import dist_matrix
from collections import Counter
q=3; G=getG(q); M=random_M01(G,1)
def lab(v, n0, per, G, S):
    if v < n0:
        j = v // per; e = v % per
        return ('L%d' % j) + ('p%d' % e if e < G.np else 'l%d' % (e - G.np))
    k = v - n0; nS=len(S)
    return ('hB%d' % S[k]) if k < nS else ('hA%d' % S[k-nS])
S=[0]
n,E,per,R=line_hub_edges(G,S,M)
D=dist_matrix(n,E); n0=3*per
c=Counter()
for a in range(n):
    for b in range(a+1,n):
        if D[a,b]>5:
            c[(lab(a,n0,per,G,S).rstrip('0123456789'), lab(b,n0,per,G,S).rstrip('0123456789'), int(D[a,b]))]+=1
print(c)
ex=[(a,b) for a in range(n) for b in range(a+1,n) if D[a,b]>5][:12]
print([(lab(a,n0,per,G,S),lab(b,n0,per,G,S)) for a,b in ex])
print('line 0 points', G.lines[0], 'M01 of those points:', [M[p] for p in G.lines[0]])

import sys, random
from collections import deque
tab = open(sys.argv[1]).read().split()
h = int(tab[0]); M = [[int(tab[1+i*h+j]) for j in range(h)] for i in range(h)]
INV = [next(y for y in range(h) if M[x][y]==0) for x in range(h)]
N = h**3
def dec(g): return (g//(h*h), (g//h)%h, g%h)
def enc(a,b,c): return (a*h+b)*h+c
def mul(s,g):
    s1,s2,s3 = dec(s); a,b,c = dec(g)
    return enc(M[s1][a], M[s2][b], M[s3][c])
def inv(s):
    a,b,c = dec(s); return enc(INV[a],INV[b],INV[c])
S = [int(v) for v in sys.argv[2].split(',')]
dist = [-1]*(2*N); dist[0]=0; q=deque([0]); reached=0
while q:
    u=q.popleft(); du=dist[u]
    if u<N:
        nb=[N+mul(s,u) for s in S]
    else:
        nb=[mul(inv(s),u-N) for s in S]
    for v in nb:
        if dist[v]<0:
            dist[v]=du+1; q.append(v)
cb=sum(1 for i in range(N,2*N) if dist[i]<0 or dist[i]>11)
ca=sum(1 for i in range(N) if dist[i]<0 or dist[i]>12)
print("reached", sum(1 for d in dist if d>=0), "of", 2*N, "cb", cb, "ca", ca, "maxd", max(dist))
print("A reached", sum(1 for i in range(N) if dist[i]>=0), "B reached", sum(1 for i in range(N,2*N) if dist[i]>=0))
from collections import Counter
print(sorted(Counter(dist).items())[:30])

# Rebuild the Haar graphs of POLISHED.md §8 from the text and check |V|, regularity, bipartite, diameter.
import itertools
from collections import deque
def cyc(n, *cycles):
    f=list(range(n))
    for c in cycles:
        for i in range(len(c)): f[c[i]]=c[(i+1)%len(c)]
    return tuple(f)
def diam_haar(G, mul, inv, S):
    idx={g:i for i,g in enumerate(G)}; n=len(G)
    adjA=[[idx[mul(s,g)] for s in S] for g in G]          # (g,A) ~ (sg,B)
    adjB=[[idx[mul(inv(s),h)] for s in S] for h in G]     # (h,B) ~ (s^-1 h, A)
    assert all(len(set(a))==len(S) for a in adjA)
    def bfs(start):  # start = ('A',i) or ('B',i); returns ecc
        dA=[-1]*n; dB=[-1]*n
        side,i=start
        (dA if side=='A' else dB)[i]=0
        dq=deque([start])
        while dq:
            s,i=dq.popleft(); d=(dA if s=='A' else dB)[i]
            nb=adjA[i] if s=='A' else adjB[i]; t='B' if s=='A' else 'A'; dt=dB if s=='A' else dA
            for j in nb:
                if dt[j]<0: dt[j]=d+1; dq.append((t,j))
        assert min(dA)>=0 and min(dB)>=0
        return max(max(dA),max(dB))
    # right multiplication is an automorphism, so eccentricities of (e,A) and (e,B) suffice
    e=G.index(next(g for g in G if mul(g,g)==g))
    return 2*n, max(bfs(('A',e)),bfs(('B',e)))
# (7,5): S4 x Z24, (f,x)(h,y) = (f o h, x+y)
perms=list(itertools.permutations(range(4)))
G=[(p,x) for p in perms for x in range(24)]
comp=lambda f,h: tuple(f[h[i]] for i in range(4))
pinv=lambda f: tuple(sorted(range(4),key=lambda i:f[i]))
mul=lambda a,b:(comp(a[0],b[0]),(a[1]+b[1])%24)
inv=lambda a:(pinv(a[0]),(-a[1])%24)
S=[(cyc(4),0),(cyc(4,(0,1),(2,3)),23),(cyc(4,(0,3,2)),0),(cyc(4,(0,2)),18),(cyc(4,(0,1,2,3)),18),(cyc(4,(1,2,3)),17),(cyc(4,(1,2)),3)]
print('(7,5) S4xZ24:', diam_haar(G,mul,inv,S))
# (9,5): Heisenberg mod 11
G=[(a,b,c) for a in range(11) for b in range(11) for c in range(11)]
mul=lambda x,y:((x[0]+y[0])%11,(x[1]+y[1])%11,(x[2]+y[2]+x[0]*y[1])%11)
inv=lambda x:((-x[0])%11,(-x[1])%11,(-x[2]+x[0]*x[1])%11)
S=[(0,0,0),(8,6,10),(7,9,3),(10,1,8),(4,4,5),(5,5,8),(6,5,4),(1,0,9),(6,10,8)]
print('(9,5) Heis11:', diam_haar(G,mul,inv,S))
# (8,5): AGL(1,7) x Z21, (x,y,z)(x',y',z') = (x+3^y x', y+y', z+z')
G=[(x,y,z) for x in range(7) for y in range(6) for z in range(21)]
mul=lambda a,b:((a[0]+pow(3,a[1],7)*b[0])%7,(a[1]+b[1])%6,(a[2]+b[2])%21)
def inv(a):
    y=(-a[1])%6; return ((-pow(3,y,7)*a[0])%7, y, (-a[2])%21)
assert all(mul(g,inv(g))==(0,0,0) for g in G)
S=[(0,0,0),(0,4,5),(6,3,18),(6,5,6),(2,4,1),(2,2,16),(4,5,12),(2,3,15)]
print('(8,5) AGL(1,7)xZ21:', diam_haar(G,mul,inv,S))

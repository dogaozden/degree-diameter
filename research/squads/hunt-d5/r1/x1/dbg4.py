import sys, random
sys.argv = ['x', 'g392_5.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
import numpy as np
def ncomp(M):
    n=M.shape[0]; par=list(range(2*n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for i,j in zip(*np.nonzero(M)): par[f(i)]=f(n+j)
    return len({f(x) for x in range(2*n)})
r = random.Random(3)
a=b=1
Aid, Bid, Arep, Brep, dcs = setup(a, b)
p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
print('dc sample', dcs[p4[0]], dcs[p2[0]], dcs[p2[1]])
for t in range(8):
    st = r.sample(p4,2)+r.sample(p2,1)
    Dl=[e for c in st for e in dcs[c]]
    M = adjacency(Dl, Arep, Bid)
    print(cost(M), 'components', ncomp(M), 'D', sorted(Dl))
# BFS validation
def bfs_counts(M, src=0):
    n=M.shape[0]
    adjA=[np.nonzero(M[i])[0] for i in range(n)]
    adjB=[np.nonzero(M[:,j])[0] for j in range(n)]
    distA={src:0}; frontier=[('A',src)]; out=[]
    dist={('A',src):0}
    q=[('A',src)]
    for d in range(1,6):
        nq=[]
        for side,v in q:
            nb = adjA[v] if side=='A' else adjB[v]
            ns = 'B' if side=='A' else 'A'
            for w in nb:
                if (ns,w) not in dist: dist[(ns,w)]=d; nq.append((ns,w))
        q=nq
    cntA=sum(1 for k,v in dist.items() if k[0]=='A' and v<=4)
    return cntA, sum(1 for k,v in dist.items() if k[0]=='A'), sum(1 for k,v in dist.items() if k[0]=='B' and v<=5)
M = adjacency(Dl, Arep, Bid)
print('BFS A-vertex0 reach<=4 (A count), A total reached, B reached<=5:', bfs_counts(M,0))
print('M row/col sums', M.sum(1)[:5], M.sum(0)[:5])

# k=2 family: points (p1,p2), lines (l1,l2), p2,l2 in Z_m, p1,l1 in {0,1,2}; l2 = F[p1][l1] - p2 (mod m), F arbitrary table.
import sys, random, time; sys.path.insert(0,'/home/user/degree-diameter/research/squads/d3D7-r1/c8')
from alg import score, write_edges, _lib
import ctypes
def build2(m, F):
    N=3*m; adj=[0]*(6*N); deg=[0]*(2*N)
    for p1 in range(3):
        for p2 in range(m):
            pi=p1*m+p2
            for l1 in range(3):
                l2=(F[p1][l1]-p2)%m; li=N+l1*m+l2
                adj[3*pi+deg[pi]]=li; deg[pi]+=1
                adj[3*li+deg[li]]=pi; deg[li]+=1
    assert all(d==3 for d in deg)
    return 2*N, adj
m=int(sys.argv[1]); trials=int(sys.argv[2]); seed=int(sys.argv[3]); out=sys.argv[4] if len(sys.argv)>4 else None
rnd=random.Random(seed); best=None; t0=time.time()
for tr in range(trials):
    F=[[rnd.randrange(m) for _ in range(3)] for _ in range(3)]
    n,adj=build2(m,F); bad,diam=score(n,adj)
    if best is None or bad<best[0]:
        best=(bad,diam,F)
        if bad==0 and out: write_edges(n,adj,out)
print('m',m,'n',2*3*m,'trials',trials,'best bad',best[0],'diam',best[1],'F',best[2],'time',round(time.time()-t0,1),flush=True)

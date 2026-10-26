import sys, collections, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load, dist_from_point
q=9; N,LP,PL,coord=load(q)
phi=np.fromfile('/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi',dtype=np.int32)
dump=sys.argv[1]; m=int(sys.argv[2])
miss=collections.defaultdict(lambda:collections.defaultdict(int))  # src -> v -> mask
for line in open(dump):
    if not line.startswith('  src'): continue
    t=line.split(); s=int(t[1].rstrip(':')); v=int(t[2][1:]); mk=int(t[6],16)
    miss[s][v]=mk
stats=collections.Counter(); bits=collections.Counter(); dist_cnt=collections.Counter()
D=np.zeros(0)
for s,d in miss.items():
    ds=dist_from_point(s,LP,PL) if s<N else None
    # need distance from line too: use generic BFS on incidence graph
    dist=np.full(2*N,-1,dtype=np.int64); dist[s]=0; frontier=[s]
    for step in range(1,7):
        nf=[]
        for x in frontier:
            nb = LP[x-N] if x>=N else PL[x]
            for y in nb:
                y = y if x>=N else N+y
                if dist[y]<0: dist[y]=step; nf.append(y)
        frontier=nf
    for v,mk in d.items():
        bits[bin(mk).count('1')]+=1
        dist_cnt[(s<N, v<N, int(dist[v]) if dist[v]>=0 else 7)]+=1
        stats[('pt' if v<N else 'ln')]+=1
print('misses per (src type==point, target type==point, dist) :')
for k,c in sorted(dist_cnt.items()): print(k,c)
print('vertices with misses', sum(stats.values()), dict(stats))
print('popcount hist of miss masks', sorted(bits.items())[:20])

import sys
H=16896
E='/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
adjA=[[] for _ in range(H)]; adjB=[[] for _ in range(H)]
with open(E) as f:
    f.readline()
    for l in f:
        u,v=map(int,l.split())
        if u>v: u,v=v,u
        v-=H; adjA[u].append(v); adjB[v].append(u)
def cover(N, side):
    # side 1: N subset of A; covered set = B-vertices within distance 3 of N (for side 0: A-vertices within 3 of N in B)
    adjN = adjA if side==1 else adjB; adjM = adjB if side==1 else adjA
    d1=set(adjN[x] for x in []) 
    cur=set(N); dist={x:0 for x in N}
    layer=set(N); seen=set(N)
    for d in range(1,4):
        nxt=set()
        for x in layer:
            for y in (adjN[x] if False else (adjM[x] if False else [])): pass
        layer=set()
        # step: alternate sides
    return None
# simple BFS on bipartite graph with global ids
def bfs_cov(N, side):
    off = 0 if side==1 else H  # N are local ids of side 'side'
    # global id: side 1 vertices (A) are local 0..H-1 ; side0 (B) local with +H in global
    seen={}
    frontier=[(x, 0) for x in N]
    for x in N: seen[('s',x)]=0
    cur=[('s',x) for x in N]  # ('s',x): vertex on side of N (N-side)
    res=set()
    layer_a=set(N); layer_b=set(); 
    # depth 1: other side
    nb1=set(); 
    for x in N: nb1.update(adjA[x] if side==1 else adjB[x])
    # depth 2: N side
    nb2=set()
    for y in nb1: nb2.update(adjB[y] if side==1 else adjA[y])
    nb3=set()
    for z in nb2: nb3.update(adjA[z] if side==1 else adjB[z])
    return nb1, nb3
for line in open(sys.argv[1]):
    if not line.strip(): continue
    N=list(map(int,line.split()))
    if N[0]>=H: N=[x-H for x in N]; side=0
    else: side=1
    nb1,nb3=bfs_cov(N,side)
    # covered S-side vertices within distance 3: nb1 (dist1, other side) ... careful: dist1 is other side, dist3 is other side too
    cov=set(nb1)|set(nb3)
    print('side',side,'N',len(N),'other-side covered',len(cov),'of',H)

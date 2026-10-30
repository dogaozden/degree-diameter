import sys, glob, os, re
from collections import Counter
D = "/home/user/degree-diameter/research/s65/groups/mc"
def load(fn):
    with open(fn) as f:
        toks = f.read().split()
    m = int(toks[0]); vals = list(map(int, toks[1:1+m*m]))
    return m, [vals[i*m:(i+1)*m] for i in range(m)]
def stats(fn):
    m, T = load(fn)
    ordr = [0]*m
    for x in range(m):
        k=1; y=x
        while y!=0:
            y=T[y][x]; k+=1
        ordr[x]= 1 if x==0 else k
    inv=[x for x in range(1,m) if ordr[x]==2]
    # central involutions
    central=0
    for x in inv:
        if all(T[x][g]==T[g][x] for g in range(m)): central+=1
    # classes of involutions
    inverse=[0]*m
    for x in range(m):
        for y in range(m):
            if T[x][y]==0: inverse[x]=y
    seen=set(); ncls=0
    for x in inv:
        if x in seen: continue
        ncls+=1
        for g in range(m):
            seen.add(T[T[g][x]][inverse[g]])
    nonab = any(T[i][j]!=T[j][i] for i in range(m) for j in range(m))
    cnt=Counter(ordr[1:])
    return m, len(inv), central, ncls, nonab, dict(sorted(cnt.items()))
lo,hi=int(sys.argv[1]),int(sys.argv[2])
for fn in sorted(glob.glob(D+"/sg_*.txt")):
    mm=re.search(r"sg_(\d+)_(\d+)\.txt",fn)
    o=int(mm.group(1))
    if lo<=o<=hi:
        m,ni,nc,ncl,nonab,cnt=stats(fn)
        name=open(fn[:-4]+".name").read().split("\n")[0]
        print(os.path.basename(fn), m, "inv=%d central=%d invcls=%d nonab=%d"%(ni,nc,ncl,nonab), "orders=",cnt, "|", name[:60], flush=True)

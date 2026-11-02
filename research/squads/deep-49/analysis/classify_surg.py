"""Classify the far pairs of a 2-vertex surgery X' of the 4,970 graph X: which deleted edge each far pair is critical for,
its slack in X, and the split (distances of its ends to the deleted edge).  Usage: classify_surg.py X.edges Xp.edges"""
import sys, subprocess
from collections import deque, Counter
def load(fn):
    L=open(fn).read().split(); n=int(L[0]); E=set()
    for i in range(1,len(L),2):
        a,b=int(L[i]),int(L[i+1]); E.add((min(a,b),max(a,b)))
    adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    return n,E,adj
def bfs(adj,s,skip=None):
    d=[-1]*len(adj); d[s]=0; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if skip and ((x,y)==skip or (y,x)==skip): continue
            if d[y]<0: d[y]=d[x]+1; q.append(y)
    return d
n0,E0,adj0=load(sys.argv[1]); n1,E1,adj1=load(sys.argv[2])
deleted=[e for e in E0 if e not in E1]
print('deleted edges',deleted,'new vertices',list(range(n0,n1)))
out=subprocess.run(['../tools/farlist',sys.argv[2],'9'],capture_output=True,text=True).stdout.split('\n')
side=bfs(adj1,0); side=[x%2 for x in side]
far=[]
for l in out:
    p=l.split()
    if len(p)==3:
        try: u,v,dd=map(int,p)
        except: continue
        far.append((u,v))
print('far pairs',len(far))
cls=Counter(); D0={}
for u,v in far:
    if u>=n0 or v>=n0: cls['involves new vertex']+=1; continue
    if u not in D0: D0[u]=bfs(adj0,u)
    du=D0[u][v]; lim=8 if side[u]==side[v] else 9
    tag='not critical for a single deleted edge'
    for (a,b) in deleted:
        dd=bfs(adj0,u,(a,b))[v]
        if dd<0 or dd>lim:
            slack=lim-du
            da=bfs(adj0,a,(a,b)); db=bfs(adj0,b,(a,b))
            if da[u]+1+db[v]==du: al,be=da[u],db[v]
            else: al,be=db[u],da[v]
            tag=f'critical slack {slack} split {tuple(sorted((al,be)))}' if slack==0 else f'critical slack {slack}'
            break
    cls[tag]+=1
for k,v in cls.most_common(): print(f'  {v:4d}  {k}')

import sys, itertools
from collections import deque
T="/home/user/degree-diameter/research/squads/own-small/tools"
L=open(T+"/bases/cubic/gh2.txt").read().split()
n,m=int(L[0]),int(L[1])
E=[(int(L[2+2*i]),int(L[3+2*i])) for i in range(m)]
adj=[[] for _ in range(n)]
for a,b in E: adj[a].append(b); adj[b].append(a)
# bipartition and BFS spanning tree from 0
col=[-1]*n; col[0]=0; par=[-1]*n; dq=deque([0]); seen={0}; treeset=set()
while dq:
    v=dq.popleft()
    for w in adj[v]:
        if w not in seen:
            seen.add(w); col[w]=1-col[v]; par[w]=v; treeset.add(frozenset((v,w))); dq.append(w)
assert len(seen)==n
bip=all(col[a]!=col[b] for a,b in E)
print("bipartite",bip,"sides",sum(1 for c in col if c==0),sum(1 for c in col if c==1),"deg",set(len(x) for x in adj),file=sys.stderr)
with open("base_tree.txt","w") as f:
    f.write(f"{n} {m}\n")
    for a,b in E:
        f.write(f"{a} {b} {1 if frozenset((a,b)) in treeset else 0} {col[a]}\n")
# group tables
def closure(gens, mul, ident):
    els=[ident]; idx={ident:0}; q=deque([ident])
    while q:
        x=q.popleft()
        for g in gens:
            y=mul(x,g)
            if y not in idx: idx[y]=len(els); els.append(y); q.append(y)
    return els, idx
def write(name, els, mul, ident):
    idx={e:i for i,e in enumerate(els)}
    assert els[0]==ident
    with open(f"groups/{name}.txt","w") as f:
        N=len(els); f.write(f"{N}\n")
        for x in els:
            f.write(" ".join(str(idx[mul(x,y)]) for y in els)+"\n")
    # sanity: associativity
    import random
    for _ in range(200):
        a,b,c=[random.choice(els) for _ in range(3)]
        assert mul(mul(a,b),c)==mul(a,mul(b,c))
    print(name,len(els),file=sys.stderr)
# Z7
write("Z7",[tuple([i]) for i in range(7)],lambda x,y:((x[0]+y[0])%7,),(0,))
# abelian products
def abmul(mods):
    return lambda x,y: tuple((a+b)%m for a,b,m in zip(x,y,mods))
def abgroup(mods):
    els=list(itertools.product(*[range(m) for m in mods]))
    return els
for name,mods in [("Z8",(8,)),("Z4xZ2",(4,2)),("Z2^3",(2,2,2))]:
    els=abgroup(mods); write(name,els,abmul(mods),tuple(0 for _ in mods))
# D4 as permutations of 4 points: r=(0 1 2 3), s=(1 3)
def pmul(p,q): # apply q then p  (composition p∘q)
    return tuple(p[q[i]] for i in range(len(q)))
r=(1,2,3,0); s=(0,3,2,1)
els,_=closure([r,s],pmul,(0,1,2,3))
write("D4",els,pmul,(0,1,2,3))
# Q8 as integer 2x2 matrices with Gaussian entries (complex ints as tuples)
def cm(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def mm(X,Y):
    return tuple(tuple(ca(cm(X[i][0],Y[0][j]),cm(X[i][1],Y[1][j])) for j in range(2)) for i in range(2))
I=((1,0),(0,0)); J=((0,0),(1,0))
qi=((0,1),(0,0)); qi=((0,1),(0,0))
Ii=(((0,1),(0,0)),((0,0),(0,-1))); Jj=(((0,0),(1,0)),((-1,0),(0,0))); one=(((1,0),(0,0)),((0,0),(1,0)))
els,_=closure([Ii,Jj],mm,one)
write("Q8",els,mm,one)

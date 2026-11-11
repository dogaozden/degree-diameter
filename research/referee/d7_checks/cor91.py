# Build the explicit Corollary 9.1-type graph (all levels H, r levels, Prop 5.2 sigma from elliptic quadric points -> Hermitian
# spread lines, Lemma 7.1 hub graph) at prime q, and write an edge list for bfs.c.
import sys, random, pickle, itertools, math
import numpy as np
q=int(sys.argv[1]); r=int(sys.argv[2]); out=sys.argv[3]; seed=int(sys.argv[4]) if len(sys.argv)>4 else 0
rng=random.Random(seed)
pts,lines=pickle.load(open(f"H{q}.pkl","rb")); D=np.load(f"D{q}.npy"); N=len(pts)
ptl=[[] for _ in range(N)]
for li,L in enumerate(lines):
    for p in L: ptl[p].append(li)
def lin(c,p): return sum(a*b for a,b in zip(c,p))%q
# elliptic quadric section (q^2+1 pairwise opposite points)
while True:
    cs=[[rng.randrange(q) for _ in range(7)] for _ in range(3)]
    S=[i for i,p in enumerate(pts) if all(lin(c,p)==0 for c in cs)]
    if len(S)==q*q+1 and all(D[a,b]==6 for a,b in itertools.combinations(S,2)): break
R=S
# Hermitian spread
while True:
    c=[rng.randrange(q) for _ in range(7)]
    if not any(c): continue
    Hp={i for i,p in enumerate(pts) if lin(c,p)==0}
    if len(Hp)!=(q**3+1)*(q+1): continue
    Ls=[li for li,L in enumerate(lines) if L<=Hp]
    if len(Ls)==q**3+1: break
Rstar=rng.sample(Ls,len(R))
assert all(D[N+a,N+b]==6 for a,b in itertools.combinations(Rstar,2))
# sigma (points -> line indices) as in Prop 5.2 (no shared points since both sets are pairwise opposite)
M={}; used=set()
for x,l in zip(R,Rstar):
    M[x]=l; used.add(l)
for x,l in zip(R,Rstar):
    G=[int(z) for z in np.where(D[x,:N]==2)[0]]; GL=[int(z)-N for z in np.where(D[N+l,N:]==2)[0]+N]
    assert len(G)==len(GL)==q*(q+1)
    rng.shuffle(GL)
    for a,b in zip(G,GL):
        assert a not in M and b not in used; M[a]=b; used.add(b)
rest=[p for p in range(N) if p not in M]; restL=[l for l in range(N) if l not in used]; rng.shuffle(restL)
for a,b in zip(rest,restL): M[a]=b
assert len(set(M.values()))==N
# Lemma 7.1 hub graph HG(K,K;delta)
delta=q-r
def kappa_s(d):
    best=None
    for s in range(2,d):
        if all(s%p for p in range(2,s)) or s in (4,8,9):   # prime powers up to 9 suffice here
            v=(s*s+s+1)*(1+(d-s-1)*d)
            if best is None or v>best[0]: best=(v,s)
    return best
kap,s=kappa_s(delta)
K=min(r*len(R),kap)
assert s in (2,3,5,7)   # prime s only in this quick builder
t=delta-s-1; u=delta-1
# PG(2,s) incidence
P2=[v for v in itertools.product(range(s),repeat=3) if any(v) and next(c for c in v if c)==1]
inc=[(i,j) for i,a in enumerate(P2) for j,b in enumerate(P2) if sum(x*y for x,y in zip(a,b))%s==0]
n0=len(P2)
Kp=K-n0; c=math.ceil(Kp/(1+u)); g=Kp-c
assert 0<=c<=n0*t and 0<=g<=u*c
# colour X ("points" side) and colour Y; vertices: X: core points 0..n0-1, then children of core lines, then depth-2 under children of core points
X=list(range(n0)); Yv=list(range(n0)); E=[]
nx=n0; ny=n0
dep1_of_points=[]; dep1_of_lines=[]
for i in range(c):           # depth-1 children of core points (colour Y)
    E.append((i%n0, ny)); dep1_of_points.append(ny); ny+=1
for i in range(c):           # depth-1 children of core lines (colour X)
    E.append((nx, i%n0)); dep1_of_lines.append(nx); nx+=1
for i in range(g):           # depth-2 under dep1_of_points (colour X)
    E.append((nx, dep1_of_points[i%c])); nx+=1
for i in range(g):           # depth-2 under dep1_of_lines (colour Y)
    E.append((dep1_of_lines[i%c], ny)); ny+=1
E+= [(a,b) for a,b in inc]
assert nx==K and ny==K
degX=[0]*K; degY=[0]*K
for a,b in E: degX[a]+=1; degY[b]+=1
assert max(degX)<=delta and max(degY)<=delta, (max(degX),max(degY))
# assemble graph: levels 0..2r, vertex (e,j) -> j*2N+e (e<N point, N+l line); B-hubs (colour X of Y) take free A-slots (points x in R),
# A-hubs take free B-slots (lines M(x))
Lv=2*r+1; base=Lv*2*N; V=lambda e,j: j*2*N+e
edges=[]
for j in range(Lv):
    for li,Lset in enumerate(lines):
        for p in Lset: edges.append((V(p,j),V(N+li,j)))
    for k in range(1,r+1):
        jj=(j+k)%Lv
        for p in range(N):
            if p in set(R): continue
            edges.append((V(p,j),V(N+M[p],jj)))
Rs=set(R)
# slots: level j has free A-slots (x,j) once per k, free B-slots (M(x),j) once per k; hub h gets slot index h in every level
Aslots=[x for k in range(r) for x in R]; Bslots=[M[x] for k in range(r) for x in R]
for h in range(K):
    for j in range(Lv):
        edges.append((base+h, V(Aslots[h],j)))          # B-hub h ~ point
        edges.append((base+K+h, V(N+Bslots[h],j)))      # A-hub h ~ line
for a,b in E: edges.append((base+a, base+K+b))
n=base+2*K
with open(out,"w") as f:
    f.write(f"{n}\n"); f.write("\n".join(f"{a} {b}" for a,b in edges)); f.write("\n")
print(f"q={q} r={r} Delta={q+1+r} |R|={len(R)} delta={delta} s={s} K={K} n={n} = {(2*r+1)*2*N} + {2*K}")

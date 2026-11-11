# Lemmas 4.1 and 4.3 tested on explicit configurations in Q(6,7) (my H(7) point set).
import numpy as np, random, sys
from itertools import combinations
from collin import Hex
q=7; H=Hex(q); P=H.pts; N=H.N; R=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 3)
def B(x,y): return int((-2*x[0]*y[0]-np.dot(x[1:4],y[4:7])-np.dot(y[1:4],x[4:7]))%q)
def Ball(y): return (-2*P[:,0]*y[0]-P[:,1:4]@y[4:7]-P[:,4:7]@y[1:4])%q
def rank(vs):
    A=[list(map(int,v)) for v in vs]; r=0
    for c in range(7):
        pr=next((i for i in range(r,len(A)) if A[i][c]%q),None)
        if pr is None: continue
        A[r],A[pr]=A[pr],A[r]; iv=pow(A[r][c],q-2,q); A[r]=[x*iv%q for x in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]%q:
                f=A[i][c]; A[i]=[(A[i][k]-f*A[r][k])%q for k in range(7)]
        r+=1
    return r
perp_of={}
def perpset(i):
    if i not in perp_of: perp_of[i]=np.where(Ball(P[i])==0)[0]
    return perp_of[i]
L=q**3-q; T3=(q+1)**2
def bound_for(cls_of, rich):
    if any(len(l)==5 for l in rich): return 5*q**4-4*L
    U=5*q**4
    for a,b in combinations(range(5),2):
        if cls_of[a]!=cls_of[b]: U-=L
    for tr in combinations(range(5),3):
        if any(cls_of[a]==cls_of[b] for a,b in combinations(tr,2)): continue
        if any(set(tr)<=l for l in rich): continue
        U+=T3
    for l in rich:
        m=len(l); U+=m*(m-1)*(m-2)//6*L
    return U
# Lemma 4.1 sampling: pair overlaps in opp(t) and triple overlaps in Q
pairs=set(); trip=set()
for _ in range(400):
    t=R.randrange(N); ys=[]
    ts=perpset(t)
    y,y2,y3=[R.choice(list(ts)) if R.random()<0.5 else R.randrange(N) for _ in range(3)]
    if len({t,y,y2,y3})<4: continue
    if rank([P[t],P[y],P[y2]])==3:
        opp=Ball(P[t])!=0
        pairs.add(int(((Ball(P[y])==0)&(Ball(P[y2])==0)&opp).sum()))
    if rank([P[y],P[y2],P[y3]])==3:
        trip.add(int(((Ball(P[y])==0)&(Ball(P[y2])==0)&(Ball(P[y3])==0)).sum()))
print("Lemma 4.1: pair overlaps in opp(t) (t not on yy'):",sorted(pairs)," min >= %d: %s"%(L,min(pairs)>=L))
print("           triple overlaps in Q (not collinear):",sorted(trip)," max <= %d: %s"%(T3,max(trip)<=T3))
# a random totally singular plane through t: t, a point x of t^perp - t, a point z of <t,x>^perp not in <t,x> with z perp... 
def ts_plane(t):
    while True:
        x=R.choice(list(perpset(t)))
        if x==t: continue
        c=np.intersect1d(perpset(t),perpset(x))
        z=int(R.choice(list(c)))
        if rank([P[t],P[x],P[z]])==3: break
    pl=[i for i in np.intersect1d(np.intersect1d(perpset(t),perpset(x)),perpset(z)) if rank([P[t],P[x],P[z],P[i]])==3]
    return pl
def ts_line_not_through(t):
    while True:
        a=R.randrange(N); b=int(R.choice(list(perpset(a))))
        if b==a: continue
        ln=[i for i in perpset(a) if B(P[i],P[b])==0 and rank([P[a],P[b],P[i]])==2]
        if t not in ln: return ln
seen={}; worst=1e9; viol=0; tested=0
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 3000):
    t=R.randrange(N); pl=ts_plane(t); ln=ts_line_not_through(t)
    src=R.choice([0,1,2])
    ys=[]
    while len(ys)<5:
        r=R.random()
        y = R.choice(pl) if r<0.55 else (R.choice(ln) if r<0.75 else R.randrange(N))
        if y!=t and y not in ys: ys.append(int(y))
    # classify
    cls_of=list(range(5))
    for a,b in combinations(range(5),2):
        if rank([P[t],P[ys[a]],P[ys[b]]])==2:
            ca,cb=cls_of[a],cls_of[b]; cls_of=[ca if c==cb else c for c in cls_of]
    col=[set(tr) for tr in combinations(range(5),3) if rank([P[ys[i]] for i in tr])==2 and len({cls_of[i] for i in tr})==3]
    # maximal collinear sets
    rich=[]
    for S in col:
        merged=False
        for l in rich:
            if len(l&S)>=2: l|=S; merged=True; break
        if not merged: rich.append(set(S))
    # merge again until stable
    changed=True
    while changed:
        changed=False
        for i in range(len(rich)):
            for j in range(i+1,len(rich)):
                if len(rich[i]&rich[j])>=2: rich[i]|=rich[j]; rich.pop(j); changed=True; break
            if changed: break
    for l in rich: assert rank([P[ys[i]] for i in l])==2
    opp=Ball(P[t])!=0
    U=np.zeros(N,bool)
    for y in ys: U|=(Ball(P[y])==0)&opp
    exact=int(U.sum()); bd=bound_for(cls_of,rich)
    tested+=1
    if exact>bd: viol+=1
    key=(tuple(sorted([cls_of.count(c) for c in set(cls_of)])),tuple(sorted(len(l) for l in rich)))
    s=seen.setdefault(key,[0,-1,1e9]); s[0]+=1; s[1]=max(s[1],exact); s[2]=min(s[2],bd-exact)
print("configurations tested %d, Bonferroni bound violated: %d"%(tested,viol))
for k,v in sorted(seen.items()): print("  type classes %-16s rich %-8s n=%5d  max exact union %5d  min(bound - exact) %d"%(k[0],k[1],v[0],v[1],v[2]))
print("types realised: %d of 17"%len(seen))

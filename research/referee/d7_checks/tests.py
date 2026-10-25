# Referee tests at prime q (default 3): SL(3,q) action, Hermitian spread, Prop 1.4, Lemma 4.1, Theorem B via Prop 5.2.
import sys, random, pickle, itertools
import numpy as np
q=int(sys.argv[1]) if len(sys.argv)>1 else 3
pts,lines=pickle.load(open(f"H{q}.pkl","rb")); D=np.load(f"D{q}.npy").astype(np.int16)
N=len(pts); P=np.array(pts); idx={tuple(p):i for i,p in enumerate(pts)}
lineidx={L:i for i,L in enumerate(lines)}
ptlines=[[] for _ in range(N)]
for li,L in enumerate(lines):
    for p in L: ptlines[p].append(li)
def norm(v):
    v=[int(c)%q for c in v]; f=next(c for c in v if c); inv=pow(f,q-2,q); return tuple((c*inv)%q for c in v)
rng=random.Random(1)
# --- SL(3,q) action (v,a,w) -> (gv, a, g^{-T} w)
def matinv3(g):
    M=[[int(x) for x in r] for r in g]
    det=(M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))%q
    if det==0: return None,0
    di=pow(det,q-2,q)
    adj=[[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m=[[M[r][c] for c in range(3) if c!=j] for r in range(3) if r!=i]
            adj[j][i]=((-1)**(i+j))*(m[0][0]*m[1][1]-m[0][1]*m[1][0])
    return np.array(adj)*di%q,det
def act(g,ginvT,p):
    v=np.array(p[:3]); w=np.array(p[4:])
    return norm(list(g.dot(v)%q)+[p[3]]+list(ginvT.dot(w)%q))
for want_det1 in (True,False):
    okall=True
    for trial in range(5):
        while True:
            g=np.array([[rng.randrange(q) for _ in range(3)] for _ in range(3)])
            gi,det=matinv3(g)
            if det and ((det==1)==want_det1): break
        ginvT=gi.T
        perm=[idx[act(g,ginvT,p)] for p in pts]
        ok=all(frozenset(perm[x] for x in L) in lineidx for L in lines)
        okall&=ok
    print(f"SL3 action preserves lines (det==1:{want_det1}):",okall)
# --- Hermitian spread: hyperplane sections, find one with q^3+1 lines of H inside forming a spread
def Qf(v): return (v[0]*v[4]+v[1]*v[5]+v[2]*v[6]-v[3]*v[3])%q
found=None
for trial in range(2000):
    c=[rng.randrange(q) for _ in range(7)]
    if not any(c): continue
    inH=[i for i,p in enumerate(pts) if sum(ci*pi for ci,pi in zip(c,p))%q==0]
    S=set(inH)
    Ls=[li for li,L in enumerate(lines) if L<=S]
    # elliptic Q^-(5,q) has (q^3+1)(q+1) points; parabolic cone etc differ
    if len(inH)==(q**3+1)*(q+1):
        found=(c,Ls); break
c,Ls=found
opp=all(D[N+a,N+b]==6 for a,b in itertools.combinations(Ls,2))
print("hyperplane",c,"points",(q**3+1)*(q+1),"H-lines inside",len(Ls),"expected",q**3+1,"pairwise opposite",opp)
spread=Ls; spreadpts=sorted(set().union(*[lines[l] for l in spread]))
# --- Lemma 4.1 checker: for all u,v exists point p notin F with D[u,p]+D[p,v]<=6 (F points); dual for lines
def lemma41(F, lines_mode=False):
    if not lines_mode: cand=[p for p in range(N) if p not in F]
    else: cand=[N+l for l in range(N) if l not in F]
    Dc=D[cand,:]   # |cand| x 2N
    fails=0
    for u in range(2*N):
        m=(Dc[:,u][:,None]+Dc).min(axis=0)
        fails+=int((m>6).sum())
    return fails
def is_segment(F):
    Fs=set(F)
    for p in F:
        ls={li for li in ptlines[p] if any(x in Fs and x!=p for x in lines[li])}
        if len(ls)>1: return False
    return True
def random_max_segment(seed):
    r=random.Random(seed); order=list(range(N)); r.shuffle(order); F=[]
    Fs=set()
    for p in order:
        Fs.add(p)
        # check segment property locally around p
        ok=True
        for x in [p]+[y for li in ptlines[p] for y in lines[li] if y in Fs and y!=p]:
            ls={li for li in ptlines[x] if any(y in Fs and y!=x for y in lines[li])}
            if len(ls)>1: ok=False;break
        if not ok: Fs.discard(p)
    return sorted(Fs)
bound=(q+1)*(q**3+1)
print("spread point set size",len(spreadpts),"bound",bound,"segment",is_segment(spreadpts))
print("Lemma 4.1 on spread points: fails",lemma41(set(spreadpts)))
for s in range(3):
    F=random_max_segment(s)
    print(f"random maximal segment set seed {s}: size {len(F)} (bound {bound}) segment {is_segment(F)} Lemma4.1 fails {lemma41(set(F))}")
    # negative control: add a point creating a turn
    Fs=set(F)
    for p in range(N):
        if p in Fs: continue
        G=Fs|{p}
        if not is_segment(sorted(G)):
            print("   + turning point: Lemma4.1 fails",lemma41(G)); break
# dual: lines through points of a partial ovoid (elliptic quadric section), plus random max dual segment set via the same routine on lines
# elliptic quadric Q^-(3,q): find 3-space with q^2+1 points, pairwise opposite
ell=None
for trial in range(5000):
    c1=[rng.randrange(q) for _ in range(7)]; c2=[rng.randrange(q) for _ in range(7)]; c3=[rng.randrange(q) for _ in range(7)]
    S=[i for i,p in enumerate(pts) if all(sum(ci*pi for ci,pi in zip(c,p))%q==0 for c in (c1,c2,c3))]
    if len(S)==q*q+1 and all(D[a,b]==6 for a,b in itertools.combinations(S,2)):
        # make sure the 3 functionals are independent: number of points of PG(3,q) in space
        ell=S; break
print("elliptic quadric section points",len(ell) if ell else None,"pairwise opposite",ell is not None)
dualF={l for p in ell for l in ptlines[p]}
print("lines through ovoid points:",len(dualF),"Lemma 4.1 (dual) fails",lemma41(dualF,True))
pickle.dump((spread,spreadpts,ell),open(f"sets{q}.pkl","wb"))

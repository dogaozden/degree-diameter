# Theorem B via Proposition 5.2: R non-collinear points with distance-4 pairs, R* lines with the same distance-4 pattern,
# M built as in Prop 5.2 with random choices; then check the transition is repaired (one-matching-edge paths, exact min-plus).
import sys, random, pickle, itertools
import numpy as np
q=int(sys.argv[1]) if len(sys.argv)>1 else 3
seed=int(sys.argv[2]) if len(sys.argv)>2 else 0
pts,lines=pickle.load(open(f"H{q}.pkl","rb")); D=np.load(f"D{q}.npy").astype(np.int16)
N=len(pts); rng=random.Random(seed)
Pt=list(range(N)); Ln=list(range(N,2*N))
G2={u:set(np.where(D[u]==2)[0].tolist()) for u in range(2*N)}
def S1ok(R,universe):  # every element of universe at distance 2 from at most two of R
    cnt={}
    for x in R:
        for z in G2[x]: cnt[z]=cnt.get(z,0)+1
    return all(c<=2 for c in cnt.values())
# random R: non-collinear with S1 and some distance-4 pairs
def grow(cands,size):
    R=[]
    order=cands[:]; rng.shuffle(order)
    for x in order:
        if any(D[x,y]==2 for y in R): continue
        if not S1ok(R+[x],None): continue
        R.append(x)
        if len(R)==size: break
    return R
size=int(sys.argv[3]) if len(sys.argv)>3 else 8
R=grow(Pt,size)
pat={(i,j) for i,j in itertools.combinations(range(len(R)),2) if D[R[i],R[j]]==4}
print("R size",len(R),"distance-4 pairs",len(pat))
# backtrack R* lines with same pattern, non-concurrent, S1
def bt(Rs):
    k=len(Rs)
    if k==len(R): return Rs
    order=Ln[:]; rng.shuffle(order)
    for l in order:
        if l in Rs: continue
        ok=True
        for i in range(k):
            d=D[Rs[i],l]
            if d==2 or ((i,k) in pat)!=(d==4): ok=False;break
        if not ok or not S1ok(Rs+[l],None): continue
        res=bt(Rs+[l])
        if res: return res
    return None
Rs=bt([])
print("R* found",Rs is not None)
f=dict(zip(R,Rs))
# Prop 5.2 construction
M={}
for x in R: M[x]=f[x]
for x,y in itertools.combinations(R,2):
    if D[x,y]==4:
        m=(G2[x]&G2[y]); mm=(G2[f[x]]&G2[f[y]]); assert len(m)==1 and len(mm)==1
        M[m.pop()]=mm.pop()
used=set(M.values())
for x in R:
    priv=[z for z in G2[x] if z not in M]; privL=[z for z in G2[f[x]] if z not in used]
    assert len(priv)==len(privL), (len(priv),len(privL))
    rng.shuffle(privL)
    for a,bb in zip(priv,privL): M[a]=bb; used.add(bb)
rest=[p for p in Pt if p not in M]; restL=[l for l in Ln if l not in used]; rng.shuffle(restL)
for a,bb in zip(rest,restL): M[a]=bb
assert len(M)==N and len(set(M.values()))==N
# check H3
print("H3 holds:",all({M[z] for z in G2[x]}==G2[M[x]] for x in R))
def repaired(M,Rset):
    A=[a for a in Pt if a not in Rset]
    Da=D[A,:]                 # level j: d(u,a)
    Dm=D[[M[a] for a in A],:] # level j': d(M(a),v)
    worst=0; fails=0
    for u in range(2*N):
        m=(Da[:,u][:,None]+1+Dm).min(axis=0)
        fails+=int((m>7).sum()); worst=max(worst,int(m.max()))
    return fails,worst
print("Theorem B transition (one-matching-edge paths): fails, worst =",repaired(M,set(R)))
# negative control: break H3 at one x by swapping M of a private point of x with a far line
x=R[0]; z=[z for z in G2[x] if all(z not in G2[y] for y in R if y!=x)][0]
far=[l for l in Ln if l not in G2[M[x]] and l not in {M[y] for y in R} and all(l not in G2[M[y]] for y in R)][0]
inv={v:k for k,v in M.items()}; w=inv[far]
M2=dict(M); M2[z],M2[w]=M[w],M[z]
print("break H3 at one point: fails, worst =",repaired(M2,set(R)))

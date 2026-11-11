# Lemma 4.1 at q=7, own sampling: pair overlaps in opp(t), triple overlaps in Q, plus exhaustive orbit-type coverage via random sampling
import numpy as np, random, sys
q=7
lines=open('/home/user/degree-diameter/research/omega_repair/hex_q7.txt').read().split('\n')
n=int(lines[0].split()[1]); nl=int(lines[0].split()[2])
P=np.array([list(map(int,l.split()[1:])) for l in lines[1+nl:1+nl+n]],dtype=np.int64)%q
G=np.zeros((7,7),dtype=np.int64)
for i,j in ((0,4),(1,5),(2,6)): G[i,j]=G[j,i]=1
G[3,3]=-2
assert ((P[:,0]*P[:,4]+P[:,1]*P[:,5]+P[:,2]*P[:,6]-P[:,3]**2)%q==0).all() and len(P)==19608
PG=(P@G)%q
def perp(i): return (PG@P[i])%q==0
rng=random.Random(5)
def collinear3(a,b,c):
    M=np.array([P[a],P[b],P[c]])%q
    # rank over F_q
    M=M.copy(); r=0
    for col in range(7):
        piv=next((i for i in range(r,3) if M[i,col]),None)
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]; M[r]=(M[r]*pow(int(M[r,col]),q-2,q))%q
        for i in range(3):
            if i!=r and M[i,col]: M[i]=(M[i]-M[i,col]*M[r])%q
        r+=1
    return r<3
pmin=10**9; tmax=0; seen2=set(); seen3=set()
for it in range(6000):
    # bias: pick some near points to hit degenerate radical types
    t=rng.randrange(n)
    pt=np.nonzero(perp(t))[0]
    y=rng.choice([rng.randrange(n), int(rng.choice(pt))])
    py=np.nonzero(perp(y))[0]
    y2=rng.choice([rng.randrange(n), int(rng.choice(py)), int(rng.choice(pt))])
    if len({t,y,y2})<3 or collinear3(t,y,y2): continue
    ov=int((perp(y)&perp(y2)&~perp(t)).sum()); pmin=min(pmin,ov); seen2.add(ov)
    tr=int((perp(y)&perp(y2)&perp(t)).sum()); tmax=max(tmax,tr); seen3.add(tr)
print("pair overlap in opp(t): min",pmin,"(claim >=",q**3-q,") values",sorted(seen2))
print("triple overlap in Q: max",tmax,"(claim <=",(q+1)**2,") values",sorted(seen3))

import sys, time, random, re, numpy as np
m1,k1,r1 = 7,3,2; m2,k2,r2 = 173,43,16
N1,N2 = m1*k1, m2*k2; N = N1*N2
idx = np.arange(N)
a1=(idx//(k1*N2))%m1; j1=(idx//N2)%k1; a2=(idx//k2)%m2; j2=idx%k2
R1=np.array([pow(r1,j,m1) for j in range(k1)]); R2=np.array([pow(r2,j,m2) for j in range(k2)])
def enc(A1,J1,A2,J2): return ((A1*k1+J1)*m2+A2)*k2+J2
def lmi(s):
    b1,l1,b2,l2=s
    return enc((b1+R1[l1]*a1)%m1,(l1+j1)%k1,(b2+R2[l2]*a2)%m2,(l2+j2)%k2)
def mul(s,t):
    b1,l1,b2,l2=s; c1,n1,c2,n2=t
    return ((b1+R1[l1]*c1)%m1,(l1+n1)%k1,(b2+R2[l2]*c2)%m2,(l2+n2)%k2)
def inv(s):
    b1,l1,b2,l2=s
    return ((-pow(pow(r1,-1,m1),l1,m1)*b1)%m1,(-l1)%k1,(-pow(pow(r2,-1,m2),l2,m2)*b2)%m2,(-l2)%k2)
def ballsize_cost(S):
    PA=list({mul(inv(t),s) for s in S for t in S}); PB=list({mul(t,inv(s)) for s in S for t in S})
    tot=0
    for P in (PA,PB):
        Ls=[lmi(p) for p in P]
        mask=np.zeros(N,bool); cur=np.array([enc(0,0,0,0)]); mask[cur]=True
        for _ in range(5):
            nx=np.unique(np.concatenate([L[cur] for L in Ls]))
            new=nx[~mask[nx]]; mask[new]=True; cur=new
            if len(cur)==0: break
        tot+=int((~mask).sum())
    return tot
S=[]
for ln in open(sys.argv[1]).read().split('\n')[1:]:
    if 'prod' not in ln: continue
    ms=re.findall(r'meta\(a=(\d+),j=(\d+)\)',ln)
    (x1,y1),(x2,y2)=ms; S.append((int(x1),int(y1),int(x2),int(y2)))
t0=time.time(); c0=ballsize_cost(S); print("start cost",c0,"eval time",round(time.time()-t0,3),flush=True)
random.seed(int(sys.argv[2])); best=c0; bestS=S[:]; ev=0; hist={}
limit=float(sys.argv[3])
while time.time()-t0<limit:
    i=random.randrange(1,5)
    g=(random.randrange(m1),random.randrange(k1),random.randrange(m2),random.randrange(k2))
    T=list(S); T[i]=g
    c=ballsize_cost(T); ev+=1
    hist[c]=hist.get(c,0)+1
    if c<best or (c==best and random.random()<0.3):
        if c<best: print("improve",c,"at eval",ev,"i",i,"g",g,flush=True)
        best=c; S=T
        if c==0: bestS=T; break
print("evals",ev,"best",best,"hist-low",sorted(hist.items())[:6])
with open(sys.argv[4],'w') as f:
    f.write("5 11 prod meta 7 3 2 meta 173 43 16 n 1 N 156219 cost %d\n"%best)
    for n,s in enumerate(S):
        f.write("%d prod[meta(a=%d,j=%d);meta(a=%d,j=%d)] z=0\n"%(0,s[0],s[1],s[2],s[3]))

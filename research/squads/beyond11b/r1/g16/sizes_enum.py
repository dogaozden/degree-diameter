import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def W(d,D):
    if D%2:
        k=(D-1)//2; w=1
        for i in range(1,k+1): w+=d*(d-1)**(2*i-1)
    else:
        k=D//2; w=sum(d*(d-1)**(2*i) for i in range(k))
    return w
def mu(N,d,D): return N*math.exp(-W(d,D)/N)
vals={3:1474,4:24360,5:297648,6:2094960,7:11012976,8:45329808,9:155250816,10:460691568,11:1241299248}
# groups: SL(2,p) (p prime >=5), times H in {1} U odd Frobenius Z_m x| Z_k (m prime, k odd>1, k | m-1)
SL=[(p*(p*p-1),f"sl {p}") for p in range(5,400) if isprime(p)]
H=[(1,"cyc")]
for m in range(3,2000,2):
    if not isprime(m): continue
    for k in range(3,m,2):
        if (m-1)%k==0 and isprime(k) or ((m-1)%k==0 and k>1 and k%2==1):
            H.append((m*k,f"meta {m} {k} r"))
import sys
d=int(sys.argv[1]); D=11
v=vals[d]
out=[]
for s,sn in SL:
    for h,hn in H:
        N=s*h
        if N<=v/2: continue
        if N>v/2*1.25: continue
        m=mu(N,d,D)
        if 6<=m<=18: out.append((N,round(m,1),sn,hn))
out.sort()
for o in out[:25]: print(o, "beats" if 2*o[0]>v else "")

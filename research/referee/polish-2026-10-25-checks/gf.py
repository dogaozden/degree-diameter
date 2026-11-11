# minimal GF(p^k) with elements 0..q-1 (polynomial basis), tables
import itertools, subprocess, os
IRR={4:(2,[1,1]),8:(2,[1,1,0]),9:(3,[2,0]),25:(5,[2,0]),27:(3,[1,1,0])}  # x^k = sum c_i x^i coefficients (low->high) after moving: x^2=x+1 for 4 etc.
def make(q):
    for p in [2,3,5,7,11,13,17,19,23]:
        if q==p:
            add=[[ (a+b)%p for b in range(q)] for a in range(q)]
            mul=[[ (a*b)%p for b in range(q)] for a in range(q)]
            return GF(q,p,add,mul)
    p,red=IRR[q]; k=len(red)
    def tov(a): return [(a//p**i)%p for i in range(k)]
    def fromv(v): return sum(c*p**i for i,c in enumerate(v))
    add=[[fromv([(x+y)%p for x,y in zip(tov(a),tov(b))]) for b in range(q)] for a in range(q)]
    def pm(a,b):
        A,B=tov(a),tov(b); r=[0]*(2*k)
        for i in range(k):
            for j in range(k): r[i+j]=(r[i+j]+A[i]*B[j])%p
        for d in range(2*k-1,k-1,-1):
            c=r[d]; r[d]=0
            if c:
                for i,ci in enumerate(red): r[d-k+i]=(r[d-k+i]+c*ci)%p
        return fromv(r[:k])
    mul=[[pm(a,b) for b in range(q)] for a in range(q)]
    return GF(q,p,add,mul)
class GF:
    def __init__(s,q,p,add,mul):
        s.q,s.p,s.A,s.M=q,p,add,mul
        s.neg=[next(b for b in range(q) if add[a][b]==0) for a in range(q)]
        s.inv=[None]+[next(b for b in range(q) if mul[a][b]==1) for a in range(1,q)]
        sq=set(mul[a][a] for a in range(1,q)); s.sq=sq
        # check field axioms quickly
        for a in range(q):
            for b in range(q):
                assert add[a][b]==add[b][a] and mul[a][b]==mul[b][a]
        for a in range(1,q): assert s.inv[a] is not None
    def a(s,*xs):
        r=0
        for x in xs: r=s.A[r][x]
        return r
    def m(s,*xs):
        r=1
        for x in xs: r=s.M[r][x]
        return r
    def sub(s,x,y): return s.A[x][s.neg[y]]
    def div(s,x,y): return s.M[x][s.inv[y]]
    def chi(s,x): return 0 if x==0 else (1 if x in s.sq else -1)
def diam(n,edges,tag=""):
    exe=os.path.join(os.path.dirname(os.path.abspath(__file__)),'apsp')
    inp="%d %d\n"%(n,len(edges))+"\n".join("%d %d"%e for e in edges)+"\n"
    out=subprocess.run([exe],input=inp,capture_output=True,text=True).stdout.strip()
    return out

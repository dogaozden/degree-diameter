def isprime(n):
    return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
import sys
def sl(q): return q*(q*q-1)
def order_mod(r,p):
    x=r%p; k=1
    while x!=1: x=x*r%p; k+=1
    return k
def frob(lo,hi):
    out=[]
    for p in range(3,hi+1):
        if not isprime(p): continue
        for k in range(3,hi//p+1,2):
            if (p-1)%k: continue
            if not (lo<=p*k<=hi): continue
            # find r of order k mod p
            rr=None
            for r in range(2,p):
                if order_mod(r,p)==k: rr=r; break
            if rr is None: continue
            out.append((p*k,p,k,rr))
    return out
q=int(sys.argv[1]); lo=int(sys.argv[2]); hi=int(sys.argv[3])
for F in sorted(frob(lo,hi)): print("SL(2,%d) x F: |F|=%d p=%d k=%d r=%d  N=%d 2N=%d"%(q,F[0],F[1],F[2],F[3],sl(q)*F[0],2*sl(q)*F[0]))

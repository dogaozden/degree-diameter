# enumerate affine semilinear groups F_q x| C_k, |G| = q*k in [529172, 560000], k | q-1,
# field automorphism x -> x^(p^i) with odd order d = e/gcd(e,i) >= 3 acting on C_k by j -> p^i j
import math
def prime_powers(maxq):
    out=[]
    for p in range(2,maxq+1):
        if all(p%r for r in range(2,int(p**0.5)+1)):
            q=p
            while q<=maxq:
                out.append((p,q)); q*=p
    return out
res=[]
for p,q in prime_powers(600000):
    e=round(math.log(q,p))
    if e<2: continue
    # divisors k of q-1 with q*k in range
    lo=-(-529172//q); hi=560000//q
    for k in range(max(lo,2),hi+1):
        if (q-1)%k: continue
        for i in range(1,e):
            d=e//math.gcd(e,i)
            if d<3 or d%2==0: continue
            # automorphism acts on C_k by multiplication by p^i; fixed set size in C_k
            fixk=sum(1 for j in range(k) if (p**i*j-j)%k==0)
            fixF=p**math.gcd(e,i)
            res.append((q*k,p,e,q,k,i,d,fixF*fixk))
res.sort()
for r in res: print("N=%d p=%d e=%d q=%d k=%d i=%d order=%d |Fix|=%d"%r)

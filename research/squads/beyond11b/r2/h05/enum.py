def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
out=[]
for base,name in [(120,'SL25'),(24,'SL23'),(336,'SL27'),(720,'SL29')]:
    lo=-(-150601//base); hi=160000//base
    for F in range(lo,hi+1):
        # F = p*k, k odd >=3, k | p-1
        for k in range(3,F+1,2):
            if F%k: continue
            p=F//k
            if p<k+1 or not isprime(p) or (p-1)%k: continue
            # primitive root
            def pw(a,e,m):
                return pow(a,e,m)
            # find element of order k
            r=None
            for g in range(2,p):
                cand=pow(g,(p-1)//k,p)
                if cand!=1 and all(pow(cand,k//q,p)!=1 for q in range(2,k+1) if k%q==0 and isprime(q)):
                    r=cand; break
            if r is None: continue
            out.append((base*F,name,p,k,r,F))
for c in sorted(out): print(c)

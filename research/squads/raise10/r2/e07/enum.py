def isprime(n):
    return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]
Qs = {'psl7':168,'sl5':120,'psl5':60,'sl3':24,'psl3':12,'meta7_3':21}
out=[]
Fs=[]
for p in range(3,2000):
    if not isprime(p): continue
    for k in divisors(p-1):
        if k>1 and k%2==1 and 200<=p*k<=5000:
            rr=None
            for r in range(2,p):
                if pow(r,k,p)==1 and all(pow(r,d,p)!=1 for d in divisors(k) if d<k):
                    rr=r;break
            if rr: Fs.append((p,k,rr,p*k))
for qn,qo in Qs.items():
    for p,k,r,fo in Fs:
        N=qo*fo
        if 47737<=N<=49000:
            out.append((N,qn,p,k,r))
for x in sorted(out): print(x)
print(len(Fs), Fs[:20])

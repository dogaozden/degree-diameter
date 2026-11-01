def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def divs(n):
    return [d for d in range(1,n+1) if n%d==0]
for lo,hi,lab in [(1047481,1150000,'6,11'),(5506489,6000000,'7,11')]:
    print('target',lab)
    for p in range(3,3000):
        if not isprime(p): continue
        for e in (2,3):
            q=p**e
            if q*3>hi: break
            if q-1 > 2*hi: continue
            for k in divs(q-1):
                if k%2==0: continue
                N=q*k
                if lo<=N<=hi: print(' p',p,'e',e,'q',q,'k',k,'N',N)

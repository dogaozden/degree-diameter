def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factors(n):
    f=[];d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return set(f)
def primroot(m):
    fs=factors(m-1)
    for g in range(2,m):
        if all(pow(g,(m-1)//q,m)!=1 for q in fs): return g
ks=[k for k in range(13,42) if isprime(k)]
res=[]
for k in ks:
    for m in range(1600000//k, 2000000//k+1):
        if isprime(m) and (m-1)%k==0:
            g=primroot(m); r=pow(g,(m-1)//k,m)
            res.append((m*k,m,k,r))
res.sort()
for x in res[:40]: print(x)
print(len(res))

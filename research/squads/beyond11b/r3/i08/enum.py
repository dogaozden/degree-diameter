def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
F=[]
for k in range(3,64,2):
    # primes p = 1 mod k, orders p*k up to ~ 1.07e6/3
    p=k+1
    while p*k<=400000:
        p+=k
        if p*k>400000: break
        if isprime(p): F.append((p*k,p,k))
F.sort()
lo,hi=1047481,1070000
# small factor orders from F with o<=2000, big factor any with N in range
res=[]
for (o,p,k) in F:
    if o>2000: break
    for (o2,p2,k2) in F:
        N=o*o2
        if N>hi: break
        if lo<=N<=hi and o2>=o:
            res.append((N,(o,p,k),(o2,p2,k2)))
res.sort()
for x in res: print(x)
print(len(res))

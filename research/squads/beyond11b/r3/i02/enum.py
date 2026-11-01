def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
out=[]
for k in range(33,46,2):
    for p in range(15168//k, 17001//k+2):
        N=p*k
        if 15168<=N<=17000 and isprime(p) and (p-1)%k==0:
            out.append((N,k,p,(p-1)%(2*k)==0))
for t in sorted(out): print("N=%d k=%d p=%d p=1mod2k=%s"%(t[0],t[1],t[2],t[3]))
print(len(out))

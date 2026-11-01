import math
def primes(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
P=primes(70000)
res=[]
for k in range(9,64,2):
    for p in P:
        if p<3 or (p-1)%k: continue
        N=p*k
        if 63649<=N<=70000:
            res.append((N,p,k))
res.sort()
for N,p,k in res:
    print(N,p,k,round(N*math.exp(-488281/N),1))
print(len(res))

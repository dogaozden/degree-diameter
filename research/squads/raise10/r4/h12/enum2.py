import sys
def sieve(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return s
def factors(n):
    f=[];d=2
    while d*d<=n:
        if n%d==0:
            f.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: f.append(n)
    return f
def primroot(p):
    fs=factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def rorder_k(p,k,g):
    return pow(g,(p-1)//k,p)
def frob(Nlo,Nhi,kmin,kmax,S):
    out=[]
    for k in range(kmin,kmax+1):
        for p in range(Nlo//k, Nhi//k+1):
            if p<3 or not S[p] or (p-1)%k: continue
            N=p*k
            if N<Nlo or N>Nhi: continue
            g=primroot(p); r=rorder_k(p,k,g)
            out.append((N,p,k,r))
    return sorted(out)
mode=sys.argv[1]
if mode=='single':
    S=sieve(1200000); L=frob(1149121,1165000,13,63,S)
elif mode=='a4':
    S=sieve(200000); L=frob(95760,97083,3,63,S)
elif mode=='z7':
    S=sieve(200000); L=frob(54720,55480,3,63,S)
for x in L: print(*x)
print("count",len(L))

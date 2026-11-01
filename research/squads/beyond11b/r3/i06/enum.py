from collections import defaultdict
LO,HI=155250,165000
def isp(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primes(a,b): return [n for n in range(a,b+1) if isp(n)]
def factor(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def primroot(q):
    phi=q-1; ps=list(factor(phi).keys())
    for g in range(2,q):
        if all(pow(g,phi//p,q)!=1 for p in ps): return g
def divs(n): return [d for d in range(1,n+1) if n%d==0]
fr=[]
for q in primes(5,HI//3):
    g=primroot(q)
    for k in divs(q-1):
        if k<3 or k%2==0 or q*k>HI//3: continue
        r=pow(g,(q-1)//k,q)
        fr.append((q*k,q,k,r))
fr.sort()
print("count",len(fr))
pairs=[]
for a in fr:
    for b in fr:
        if a[0]<=b[0] and LO<=a[0]*b[0]<=HI and max(a[2],b[2])>=13:
            pairs.append((a[0]*b[0],a,b))
print("pairs",len(pairs))
byshape=defaultdict(list)
for N,a,b in pairs:
    byshape[(min(a[2],b[2]),max(a[2],b[2]))].append((N,a,b))
for s in sorted(byshape): print(s,len(byshape[s]), byshape[s][0])

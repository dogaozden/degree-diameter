def primes(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
def pfac(n):
    f=[];d=2
    while d*d<=n:
        if n%d==0:
            f.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: f.append(n)
    return f
F = []
for p in primes(20000):
    if p < 3: continue
    for k in range(3, p, 2):
        if (p-1) % k: continue
        found = None
        for r in range(2, p):
            if pow(r, k, p) == 1 and all(pow(r, k//q, p) != 1 for q in pfac(k)):
                found = r; break
        if found is None: continue
        F.append((p*k, p, k, found))
F.sort()
print("num frobenius odd groups:", len(F))
for lo,hi,name in [(1047481,1100000,'6,11'),(5506489,5800000,'7,11')]:
    singles = [f for f in F if lo <= f[0] <= hi]
    print(name, "single meta N in range:", [(f[1],f[2],f[3],f[0]) for f in singles][:20])
    pairs = []
    for a in F:
        if a[0] < 200: continue
        for b in F:
            if b[0] < a[0]: continue
            if b[0] < 200: continue
            N = a[0]*b[0]
            if N > hi: break
            if lo <= N <= hi: pairs.append((N, a[1:], b[1:]))
    print(name, "products count", len(pairs))
    for x in pairs[:60]: print(x)
    for n in [3,5,7,9,11,13]:
        for a in F:
            if lo <= a[0]*n <= hi: print(name, "F x Z_%d" % n, a[0]*n, a[1:])

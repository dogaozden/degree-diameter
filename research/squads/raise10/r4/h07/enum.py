import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factors(n):
    f=[];i=2
    while i*i<=n:
        while n%i==0: f.append(i); n//=i
        i+=1
    if n>1: f.append(n)
    return set(f)
def primroot(p):
    fs=factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
done = {(6397,41),(5851,45),(9049,29),(10501,25),(9721,27),(5641,47)}
out=[]
for k in range(31,64):
    for N in range(262081, 266001):
        if N % k: continue
        p = N//k
        if not isprime(p) or (p-1) % k: continue
        if (p,k) in done: continue
        g = primroot(p)
        r = pow(g,(p-1)//k,p)
        out.append((N,p,k,r))
out.sort()
for t in out: print(*t)
print("count",len(out), file=sys.stderr)

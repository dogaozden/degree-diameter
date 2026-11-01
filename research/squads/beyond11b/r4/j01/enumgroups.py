def isp(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=1;o=0
    while True:
        x=x*r%p;o+=1
        if x==1: return o
out=[]
for k in range(13,28,2):
    for p in range(2,16001):
        if (p-1)%k or not isp(p): continue
        N=p*k
        if N<15168 or N>16000: continue
        # pick r of order exactly k mod p (smallest)
        rs=[r for r in range(2,p) if order(r,p)==k]
        if not rs: continue
        out.append((N,p,k,rs[0],len(rs)))
out.sort()
for t in out: print("N=%d p=%d k=%d r=%d (#r=%d)"%t)
print(len(out))

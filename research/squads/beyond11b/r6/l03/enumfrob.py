import math
def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True
def ord_ok(r,k,p):
    # exact order k
    if pow(r,k,p)!=1: return False
    for q in range(2,k+1):
        if k%q==0 and isprime(q) and pow(r,k//q,p)==1: return False
    return True
out=[]
for k in range(3,64):
    lo=528444//k; hi=532000//k+1
    for p in range(max(lo,k+1),hi+1):
        if (p-1)%k==0 and isprime(p):
            N=p*k
            if 528444<=N<=532000:
                for a in range(2,50):
                    r=pow(a,(p-1)//k,p)
                    if r>1 and ord_ok(r,k,p):
                        out.append((N,p,k,r)); break
out.sort()
for o in out[:40]: print('N=%d Z%d x| Z%d r=%d vertices %d'%(o[0],o[1],o[2],o[3],2*o[0]))
print(len(out))

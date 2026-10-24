# metacyclic Z_m x|_r Z_k parameters: r^k = 1 mod m, r of exact order k (we just need r^k=1)
import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factor(n):
    f=[];p=2
    while p*p<=n:
        while n%p==0: f.append(p); n//=p
        p+=1
    if n>1: f.append(n)
    return set(f)
def prim_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def metas(k, lo, hi):
    # prime m = p with k | p-1 : Z_p x| Z_k, r of order k
    out=[]
    for p in range(lo,hi):
        if isprime(p) and (p-1)%k==0:
            g=prim_root(p); r=pow(g,(p-1)//k,p); out.append((p,k,r,p*k))
    return out
if __name__=='__main__':
    k=int(sys.argv[1]); lo=int(sys.argv[2]); hi=int(sys.argv[3])
    for row in metas(k,lo,hi)[:int(sys.argv[4]) if len(sys.argv)>4 else 5]: print(*row)

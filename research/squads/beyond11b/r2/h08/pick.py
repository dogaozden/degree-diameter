import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r; o=1
    while x!=1: x=x*r%p; o+=1
    return o
def root(p,k):
    # element of exact order k mod p (k | p-1)
    for g in range(2,p):
        r=pow(g,(p-1)//k,p)
        if order(r,p)==k: return r
    return None
NMIN=5506489
for k in map(int,sys.argv[1:]):
    p=NMIN//k+1
    while True:
        if (p-1)%k==0 and isprime(p): break
        p+=1
    r=root(p,k)
    print(f"meta {p} {k} {r}  N={p*k}")

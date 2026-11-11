import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=1
    for e in range(1,p+1):
        x=x*r%p
        if x==1: return e
c=[(15451,328,15),(17837,5686,13),(11047,638,21),(5659,260,41),(13669,812,17),(5419,291,43),(8641,192,27),(4591,125,51),(6007,232,39)]
for p,r,k in c:
    print(p,r,k,"prime" if isprime(p) else "COMPOSITE", "p-1%k=",(p-1)%k, "ord(r)=",order(r%p,p) if r%p else 0, "N=",p*k)

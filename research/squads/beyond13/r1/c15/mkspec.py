import sys
def isprime(x):
    if x<3: return x==2
    if x%2==0: return False
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
k=int(sys.argv[1]); t=int(sys.argv[2])
best=None
for m in range(t-400,t+400):
    if m%2==0 or not isprime(m) or (m-1)%k: continue
    if best is None or abs(m*k-t)<abs(best*k-t): best=m
m=best
x=2
while True:
    r=pow(x,(m-1)//k,m)
    if r!=1: break
    x+=1
print(m,k,r,m*k)

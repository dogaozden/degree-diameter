import sys
def isprime(x):
    if x<3: return x==2
    if x%2==0: return False
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def prim_root_order_k(m,k):
    for x in range(2,m):
        r=pow(x,(m-1)//k,m)
        if r!=1: return r
# (k, target |G|)
for k,target in [(3,26500),(5,15900),(7,11300),(9,8800),(11,7200),(13,6100),(15,5300),(21,3800)]:
    best=None
    for m in range(target-400,target+400):
        if m%2==0 or not isprime(m): continue
        if (m-1)%k: continue
        if best is None or abs(m*k-79464)<abs(best*k-79464): best=m
    m=best
    print(f"k={k} m={m} r={prim_root_order_k(m,k)} G={m*k} N_vertices={2*m*k}")

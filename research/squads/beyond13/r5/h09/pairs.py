import sys, math
sys.path.insert(0,'/home/user/degree-diameter/research/frontier/beyond13/meta')
def isp(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def W(d,D):
    if D%2==0: return sum(d*(d-1)**(2*i) for i in range(D//2))
    return 1+sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
d,D=6,11
# odd-order Frobenius groups Z_m x|_r Z_k, k odd prime, m prime = 1 mod k, N=mk
G=[]
for k in [3,5,7,11,13,17,19,23,29,31,37,41,43]:
    for m in range(2*k+1, 3000, 2*k):
        if isp(m):
            # need r of order k mod m
            for g in range(2,m):
                r=pow(g,(m-1)//k,m)
                if r!=1: break
            G.append((m*k,m,k,r))
G.sort()
import itertools
res=[]
lo,hi=1047480,1100000
for a in G:
    for b in G:
        if a[0]*b[0]>=lo and a[0]*b[0]<=hi and a[0]<=b[0] and a[0]>=100:
            res.append((a[0]*b[0],a,b))
res.sort()
print(len(res), file=sys.stderr)
for N,a,b in res[:4000:]:
    mu=N*math.exp(-W(d,D)/N)
    if N>=1047481:
        pass
    print(N, f"{a[1]} {a[2]} {a[3]}", f"{b[1]} {b[2]} {b[3]}", f"mu={mu:.2f}")

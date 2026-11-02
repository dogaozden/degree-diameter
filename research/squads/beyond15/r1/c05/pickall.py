# For each cell (d,D) and prime k, choose Z_m x|_r Z_k (m prime, m = 1 mod 2k, r of order k) with mu closest to 8.
import math, json
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a, dd, x)
        if y in (1, x-1): continue
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: break
        else: return False
    return True
def W(d, D):
    if D % 2 == 0: return sum(d*(d-1)**(2*i) for i in range(D//2))
    return 1 + sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
cells={(4,15):6.4e5,(4,16):1.72e6,(5,15):2.4e7,(5,16):8.8e7}
ks=[13,19,31,43,61,97,151,211,307]
res={}
for (d,D),N0 in cells.items():
    w=W(d,D)
    mu=lambda N: N*math.exp(-w/N)
    for k in ks:
        best=None
        for fac in (1.25,2.5):
          if best: break
          lo,hi=N0/fac,N0*fac
          m=int(lo//k); m-= m%(2*k); m+=1
          while m*k<=hi:
              if isp(m):
                  N=m*k
                  if N>=lo:
                      # r of order k
                      g=2
                      while True:
                          r=pow(g,(m-1)//k,m)
                          if r!=1: break
                          g+=1
                      v=mu(N)
                      if v>0:
                          c=abs(math.log(v/8))
                          if best is None or c<best[0]: best=(c,m,k,r,N,round(v,2))
              m+=2*k
        if best: res[f"{d},{D},{k}"]=best[1:]; print(d,D,k,best[1:],flush=True)
        else: print(d,D,k,'none',flush=True)
json.dump(res,open('groups.json','w'),indent=1)

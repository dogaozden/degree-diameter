import sys
from math import gcd
def metas(lo,hi):
    out=[]
    for N in range(lo,hi+1):
        for k in range(2,N):
            if N%k: continue
            m=N//k
            if m<2: continue
            seen=set()
            for r in range(1,m):
                if gcd(r,m)!=1 or pow(r,k,m)!=1%m: continue
                c=min(pow(r,j,m) for j in range(1,k+1) if gcd(j,k)==1)
                if c in seen: continue
                seen.add(c); out.append((N,m,k,c))
    return out
if __name__=="__main__":
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    G=metas(lo,hi)
    print(len(G))
    # count those with an order-4 unit mod m (u^4=1, u^2!=1)
    c4=[g for g in G if any(pow(u,4,g[1])==1%g[1] and pow(u,2,g[1])!=1%g[1] for u in range(1,g[1]) if gcd(u,g[1])==1)]
    c2=[g for g in G if any(pow(u,2,g[1])==1%g[1] and u%g[1]!=1%g[1] for u in range(1,g[1]) if gcd(u,g[1])==1)]
    print("order4 units:",len(c4),"order2 nontrivial units:",len(c2))

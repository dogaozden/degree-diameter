import math
G={}
for N in range(9,1600,2):
    for k in range(3,N+1,2):
        if N%k: continue
        m=N//k
        if m<3 or m%2==0 or k>m: continue
        for r in range(2,m):
            if math.gcd(r,m)==1 and pow(r,k,m)==1:
                G.setdefault(N,[]).append((m,k,r)); break
lo,hi=14879,15500
out=[]
for a in G:
    for b in G:
        if a>b: continue
        N=a*b
        if lo<=N<=hi:
            for x in G[a][:2]:
                for y in G[b][:2]:
                    out.append((N,a,x,b,y))
out.sort()
seen=0
for o in out[:40]: print(o)
print(len(out))

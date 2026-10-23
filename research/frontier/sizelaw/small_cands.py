"""Small groups for haar_gen3: metacyclic Z_m x|_r Z_k (r^k=1 mod m, r != 1 or k=1 ... nonabelian preferred) x Z_n,
plus the matrix/affine families from cands_gen.py. Order window [lo,hi]. Output 'spec|N'."""
import sys, math, subprocess
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=set()
for N in range(lo,hi+1):
    for k in range(2,N):
        if N%k: continue
        m=N//k
        if m<3: continue
        seen=set()
        for r in range(2,m):
            if math.gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            # skip r whose subgroup <r> was already used (isomorphic up to choice of generator of Z_k)
            sub=frozenset(pow(r,j,m) for j in range(k))
            if sub in seen: continue
            seen.add(sub); out.add((N,'meta %d %d %d 1'%(m,k,r)))
p=subprocess.run(['python3','cands_gen.py',str(lo),str(hi)],capture_output=True,text=True).stdout
for l in p.split():
    pass
for l in p.splitlines():
    s,N=l.split('|'); out.add((int(N),s))
for N,s in sorted(out): print('%s|%d'%(s,N))

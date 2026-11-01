import math
W=61035156
lo,hi=4683121,4900000
def primes(a,b):
    s=[]
    for n in range(max(2,a),b+1):
        if n<2: continue
        if all(n%d for d in range(2,int(n**0.5)+1)): s.append(n)
    return s
out=[]
for k in range(2,64):
    for p in primes(lo//k, hi//k+2):
        N=p*k
        if lo<=N<=hi and (p-1)%k==0:
            out.append((N, f"meta {p} {k} r", round(N*math.exp(-W/N),2), f"Z{p} x| Z{k}"))
def psl(q): return q*(q*q-1)//2
for q in primes(40,130):
    base=psl(q)
    for m in range(1,200):
        N=base*m
        if lo<=N<=hi: out.append((N, f"prod psl {q} meta {m} 1 1", round(N*math.exp(-W/N),2), f"PSL(2,{q}) x Z{m}"))
for N,s,mu,name in sorted(out):
    print(N,mu,name,"|",s)

import itertools
def primerange(a,b):
    for n in range(max(a,2),b):
        if all(n%d for d in range(2,int(n**0.5)+1)): yield n
LO, HI = 15168, 17000
A=[]
for k in range(47,64,2):
    for p in primerange(3, HI//k+2):
        if (p-1)%k==0 and LO <= p*k <= HI:
            A.append((p,k,p*k))
print("single:",A)
M=[]
for k in range(3,64,2):
    for p in primerange(3, 8500//k+2):
        if (p-1)%k==0 and p*k<=8500:
            M.append((p,k,p*k))
print("nM",len(M))
P=[]
for (p1,k1,n1),(p2,k2,n2) in itertools.combinations_with_replacement(M,2):
    N=n1*n2
    big_k = k1 if n1>=n2 else k2
    if LO<=N<=HI and big_k>=13:
        P.append((p1,k1,p2,k2,N))
print("prod count",len(P))
for x in sorted(P,key=lambda t:-max(t[1],t[3]))[:60]: print(x)
Q=[]
for (p1,k1,n1),(p2,k2,n2) in itertools.combinations_with_replacement(M,2):
    N=n1*n2
    if LO<=N<=HI: Q.append((p1,k1,p2,k2,N))
print("any",len(Q))
for x in Q[:40]: print(x)

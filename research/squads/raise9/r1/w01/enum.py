import math, sys
def isprime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
def pp(q):
    # prime power? return (p,k) or None
    for p in range(2, q+1):
        if q % p == 0:
            x = q; k = 0
            while x % p == 0: x //= p; k += 1
            return (p, k) if x == 1 else None
    return None
def W(d, D):
    return 1 + sum(d*(d-1)**(2*i-1) for i in range(1, (D-1)//2+1))
d, D = int(sys.argv[1]), int(sys.argv[2])
bar = int(sys.argv[3]); slack = float(sys.argv[4]); nmax = int(sys.argv[5])
w = W(d, D)
# group list: (name, order)
G = []
for q in range(4, 400):
    if pp(q) is None: continue
    p, k = pp(q)
    G.append((f"sl {q}", q*(q*q-1)))
    if q % 2 == 1:
        G.append((f"psl {q}", q*(q*q-1)//2))
        
small = [g for g in G if int(g[0].split()[1]) <= 13]
out = []
for a in small:
    for b in G:
        for n in range(1, nmax+1):
            N = a[1]*b[1]*n
            if N < bar or N > bar*(1+slack): continue
            if N > 4e7: continue
            mu = N*math.exp(-w/N)
            out.append((N, f"prod {a[0]} | {b[0]} | Z{n}", mu))
out.sort()
for N, s, mu in out:
    print(f"N={N} 2N={2*N} mu={mu:.2f} {s}")

import math
def isprime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
def prim_root(p):
    fac = [q for q in range(2, p) if (p-1) % q == 0 and isprime(q)]
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
def W(d,D):
    return 1 + sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
out = []
ks = list(range(29, 64, 2)) + list(range(30, 63, 2))
for k in ks:
    lo = math.ceil(63649 / k); hi = 67000 // k
    for p in range(lo, hi+1):
        if not isprime(p) or (p-1) % k: continue
        g = prim_root(p); r = pow(g, (p-1)//k, p)
        assert pow(r, k, p) == 1 and all(pow(r, j, p) != 1 for j in range(1, k))
        N = p*k
        out.append((N, p, k, r, k % 2 == 1))
out.sort()
for N,p,k,r,odd in out:
    print(f"{N} {p} {k} {r} {'odd' if odd else 'even'} mu={N*math.exp(-W(6,9)/N):.1f}")
print(len(out), "candidates")

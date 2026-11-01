import math, sys
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond')
from plan import W
d, D = 19, 8
w = W(d, D)
lo_mu, hi_mu = 12.5, 26.0
def mu(N): return N*math.exp(-w/N)
def Nlo():
    lo, hi = 1e6, 1e9
    for _ in range(200):
        m = math.sqrt(lo*hi)
        if mu(m) < lo_mu: lo = m
        else: hi = m
    return lo
def Nhi():
    lo, hi = 1e6, 1e9
    for _ in range(200):
        m = math.sqrt(lo*hi)
        if mu(m) < hi_mu: lo = m
        else: hi = m
    return lo
NL, NH = Nlo(), Nhi()
print("W", w, "N range", int(NL), int(NH), file=sys.stderr)
def isprime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
def prime_powers(lim):
    out = []
    for q in range(2, lim+1):
        for p in range(2, q+1):
            if isprime(p):
                if q % p == 0:
                    x = q
                    while x % p == 0: x //= p
                    if x == 1: out.append(q)
                    break
    return out
def good_n(n, k=3):
    if n == 1: return True
    m, r = n, 2
    while r*r <= m:
        while m % r == 0:
            if r % k != 1: return False
            m //= r
        r += 1
    return m == 1 or m % k == 1
PP = prime_powers(600)
sl = lambda q: q*(q*q-1)
out = []
# single SL/PSL/PGL x Z_n with q prime power
for q in PP:
    for fam, base in (("sl", sl(q)), ("pgl", sl(q)), ("psl", sl(q)//2)):
        if q == 2 and fam == "psl": continue
        n = 1
        while base*n <= NH*1.0:
            N = base*n
            if N >= NL and good_n(n) and n >= 1:
                # gcd(q,n)=1 for p-part
                if math.gcd(q, n) == 1 and (q % 2 == 0 or True):
                    out.append((N, f"{fam} {q} n{n}", mu(N)))
            n += 1
# prod sl q1 sl q2 n
for i, q1 in enumerate(PP):
    for q2 in PP:
        if q2 < q1: continue
        P = sl(q1)*sl(q2)
        if P > NH: continue
        n = 1
        while P*n <= NH:
            N = P*n
            if N >= NL and good_n(n) and math.gcd(q1*q2, n) == 1:
                out.append((N, f"prod sl {q1} sl {q2} n{n}", mu(N)))
            n += 1
out.sort()
for N, name, m in out:
    print(f"{N:>12,}  2N={2*N:>12,}  mu={m:6.2f}  {name}")
print("count", len(out), file=sys.stderr)

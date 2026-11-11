import math, sys
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond')
from plan import W
d, D = 19, 8
w = W(d, D)
def mu(N): return N*math.exp(-w/N)
def solve(target):
    lo, hi = 1e6, 1e9
    for _ in range(200):
        m = math.sqrt(lo*hi)
        if mu(m) < target: lo = m
        else: hi = m
    return lo
NL, NH = solve(12.5), solve(26.0)
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
        ps = [p for p in range(2, q+1) if q % p == 0 and isprime(p)][:1]
        if not ps: continue
        p = ps[0]; x = q
        while x % p == 0: x //= p
        if x == 1: out.append(q)
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
PP = prime_powers(120)
sl = lambda q: q*(q*q-1)
out = []
for q in PP:
    for fam, base in (("sl", sl(q)), ("pgl", sl(q)), ("psl", sl(q)//2)):
        if fam == "psl" and q % 2 == 0: continue
        if base < 1000: continue
        for n in range(max(1, math.ceil(NL/base)), min(int(NH//base), 40*q)+1):
            if good_n(n) and math.gcd(q, n) == 1:
                out.append((base*n, f"{fam} {q} n{n}"))
for q1 in PP:
    for q2 in PP:
        if q2 < q1: continue
        P = sl(q1)*sl(q2)
        if P > NH or P < 1000: continue
        for n in range(max(1, math.ceil(NL/P)), min(int(NH//P), 40*max(q1,q2), 3000)+1):
            if good_n(n) and math.gcd(q1*q2, n) == 1:
                out.append((P*n, f"prod sl {q1} sl {q2} n{n}"))
out.sort()
for N, name in out:
    print(f"{N:>12,} 2N={2*N:>12,} mu={mu(N):6.2f} {name}")
print("count", len(out), file=sys.stderr)

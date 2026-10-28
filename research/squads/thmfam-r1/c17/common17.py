import math, itertools, subprocess, os
HF = '/home/user/degree-diameter/research/theorems/haar_families'
W = (0, -1, 1, -1)          # w = [[0,-1],[1,-1]], order 3 in SL(2,Z)
WI = (-1, 1, -1, 0)         # w^-1 = w^2
def imul(X, Y):
    a,b,c,d = X; e,g,h,i = Y
    return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
def conjw(X): return imul(imul(W, X), WI)
def orbit(X):
    X1 = conjw(X); X2 = conjw(X1); return [X, X1, X2]
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5)+1))
def primes(a, b): return [p for p in range(a, b+1) if isprime(p)]
def primroot(q):
    fs = [f for f in range(2, q) if (q-1) % f == 0 and isprime(f)]
    for g in range(2, q):
        if all(pow(g, (q-1)//f, q) != 1 for f in fs): return g
def cuberoot(m):
    if m == 1: return 0
    if m % 3 != 1 or not isprime(m): return None
    for r in range(2, m):
        if pow(r, 3, m) == 1: return r
def mrule(q):   # largest prime <= q with p = 1 mod 3
    return max(p for p in primes(3, q) if p % 3 == 1)
def mrule_any(q):  # largest prime <= q
    return max(primes(3, q))
def excess_of(q, m, lines, group='sl', Delta=6):
    inp = '\n'.join(lines) + '\n'
    r = subprocess.run([os.path.join(HF, 'haar_ecc'), group, str(q), str(m)], input=inp, capture_output=True,
                       text=True, timeout=900)
    import re
    mm = re.search(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not mm: return None
    d, eA, eB, cA, cB, order = (int(mm.group(i)) for i in range(1, 7))
    conn = mm.group(7); diam = int(mm.group(8))
    if cA != cB: return None
    G = cA // 2
    diam = max(eA, eB)
    return {'q': q, 'm': m, 'Delta': d, 'G': G, 'diam': diam, 'connected': conn,
            'excess': diam - math.log(G) / math.log(d - 1)}

import math, sys
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond')
from plan import W
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def good_n(n, k=3):
    m, r = n, 2
    while r * r <= m:
        while m % r == 0:
            if r % k != 1: return False
            m //= r
        r += 1
    return m == 1 or m % k == 1
w = W(19, 8)
classes = {'n1': lambda n: n == 1, 'n7-31': lambda n: 7 <= n <= 31, 'n100-300': lambda n: 100 <= n <= 300, 'n1000+': lambda n: n >= 1000}
best = {}
for p in range(5, 2000):
    if not isprime(p) or p == 3 or ((p-1)*(p+1)) % 3: continue
    for fam, base in (("sl", p*(p*p-1)), ("psl", p*(p*p-1)//2)):
        for n in range(1, 20000):
            N = base * n
            if N > 60e6: break
            if math.gcd(p, n) != 1 or not (n == 1 or good_n(n)): continue
            m = N * math.exp(-w / N)
            if m < 17 or m > 31: continue
            for cn, f in classes.items():
                if f(n):
                    best.setdefault((cn, fam), []).append((abs(m - 24), fam, p, n, m))
for key in sorted(best):
    lst = sorted(best[key])[:3]
    for e in lst:
        print(key, f"{e[1]} {e[2]} {e[3]} mu={e[4]:.2f}")

"""Table of the cyclotomic bound at Delta=3: for each D and each k <= KMAX and each o | k (o >= 2), B(k, o) and the
largest prime p allowed (p <= B/k, p = 1 mod o), i.e. the largest group Z_p x| Z_k with action order o that can have a
cubic Haar graph of diameter D.  Usage: python3 cyclotable.py D KMAX"""
import sys
import cyclobound
from cyclobound import bound
if "--fiber" in sys.argv:
    cyclobound.FIBER = True
    sys.argv.remove("--fiber")
def isprime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))
D, KMAX = int(sys.argv[1]), int(sys.argv[2])
print(f'# Delta=3 D={D}: k o B(k,o) pmax(=largest prime p = 1 mod o with p*k <= B) Nmax=pmax*k')
best = []
for k in range(2, KMAX + 1):
    for o in range(2, k + 1):
        if k % o:
            continue
        B, j = bound(3, D, k, o)
        pm = max([p for p in range(o + 1, B // k + 1) if isprime(p) and (p - 1) % o == 0], default=0)
        print(f'{k:3d} {o:3d} {B:6d} {pm:5d} {pm * k:6d}', flush=True)
        best.append((pm * k, k, o, pm))
best.sort(reverse=True)
print('# largest allowed N:', best[:8])

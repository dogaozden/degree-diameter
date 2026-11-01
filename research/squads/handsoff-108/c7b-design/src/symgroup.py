# symgroup.py (worker c7b): pick a cyclic subgroup K of prime order p of Aut(H(q)) (side-preserving, i.e. in G2(q))
# acting FIXED-POINT-FREELY on points and lines. Uses the BLISS generators from autg.py (runs/autgens_q{q}.txt).
# usage: python3 -I src/symgroup.py Q PRIME [TRIES] [SEED]  -> writes runs/K_q{q}_p{PRIME}.txt (one permutation of 2N)
import sys, os, random
HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
q, P = int(sys.argv[1]), int(sys.argv[2])
tries = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
gens = [list(map(int, line.split())) for line in open(os.path.join(HERE, 'runs', 'autgens_q%d.txt' % q))]
n2 = len(gens[0]); N = n2 // 2
def mul(a, b):   # apply a then b
    return [b[a[i]] for i in range(n2)]
def inv(a):
    r = [0] * n2
    for i, x in enumerate(a): r[x] = i
    return r
def power(a, e):
    r = list(range(n2)); base = a
    while e:
        if e & 1: r = mul(r, base)
        base = mul(base, base); e >>= 1
    return r
def cycles(a):
    seen = [False] * n2; out = []
    for i in range(n2):
        if not seen[i]:
            c = 0; j = i
            while not seen[j]:
                seen[j] = True; j = a[j]; c += 1
            out.append(c)
    return out
from math import gcd
found = None
for t in range(tries):
    x = list(range(n2))
    for _ in range(40):
        g = rng.choice(gens)
        if rng.random() < 0.5: g = inv(g)
        x = mul(x, g)
    if x[0] >= N:          # side swapping (duality): skip
        continue
    cyc = cycles(x)
    lcm = 1
    for c in cyc: lcm = lcm * c // gcd(lcm, c)
    if lcm % P: continue
    y = power(x, lcm // P)
    cy = cycles(y)
    if all(c == P for c in cy):      # fixed-point-free on all vertices of order P
        found = y; break
if found is None:
    print('no fixed-point-free element of order', P, 'in', tries, 'tries'); sys.exit(1)
print('q=%d K order %d semiregular on %d points, orbits on points %d; lines %d' %
      (q, P, N, N // P, N // P))
with open(os.path.join(HERE, 'runs', 'K_q%d_p%d.txt' % (q, P)), 'w') as f:
    f.write(' '.join(map(str, found)) + '\n')

# symgroup_np.py (worker c7b): numpy version of symgroup.py for large q (H(7): 39216 vertices).
# usage: python3 -I src/symgroup_np.py Q PRIME [TRIES] [SEED]
import sys, os, random
import numpy as np
HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
q, P = int(sys.argv[1]), int(sys.argv[2])
tries = int(sys.argv[3]) if len(sys.argv) > 3 else 200
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
gens = [np.array(list(map(int, line.split())), dtype=np.int64) for line in open(os.path.join(HERE, 'runs', 'autgens_q%d.txt' % q))]
n2 = len(gens[0]); N = n2 // 2
ginv = []
for g in gens:
    r = np.empty_like(g); r[g] = np.arange(n2); ginv.append(r)
def cycles_lcm(a):
    seen = np.zeros(n2, bool); lens = []
    for i in range(n2):
        if not seen[i]:
            c = 0; j = i
            while not seen[j]:
                seen[j] = True; j = a[j]; c += 1
            lens.append(c)
    return lens
from math import gcd
def power(a, e):
    r = np.arange(n2); base = a.copy()
    while e:
        if e & 1: r = base[r]
        base = base[base]; e >>= 1
    return r
found = None
for t in range(tries):
    x = np.arange(n2)
    for _ in range(40):
        i = rng.randrange(len(gens))
        g = ginv[i] if rng.random() < 0.5 else gens[i]
        x = g[x]
    if x[0] >= N: continue
    lens = cycles_lcm(x)
    lcm = 1
    for c in lens: lcm = lcm * c // gcd(lcm, c)
    if lcm % P: continue
    y = power(x, lcm // P)
    ly = cycles_lcm(y)
    if all(c == P for c in ly):
        found = y; break
    # also record how many tries
if found is None:
    print('no fixed-point-free element of order', P, 'in', tries, 'tries'); sys.exit(1)
print('q=%d K order %d semiregular on %d points (orbits %d); found at try %d' % (q, P, N, N // P, t))
with open(os.path.join(HERE, 'runs', 'K_q%d_p%d.txt' % (q, P)), 'w') as f:
    f.write(' '.join(map(str, found.tolist())) + '\n')

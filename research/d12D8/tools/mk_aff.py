"""hexagon H(q) + 2 random hop matchings, fibre Z_N, affine twists.
mode: trans (all maps translations, = regular lift, control) | afh (hexagon edges random affine a x + b, hops translations
by random b) | afall (all edges random affine) | unif A (hexagon a = A fixed, random b; hops translation)."""
import sys, random
from math import gcd
from hexlib import load_hex
q, N, mode, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
A = int(sys.argv[6]) if len(sys.argv) > 6 else 1
random.seed(seed)
n, lines = load_hex(q)
units = [a for a in range(1, N) if gcd(a, N) == 1]
def mp(kind):
    if kind == 'trans': return 1, random.randrange(N)
    if kind == 'aff': return random.choice(units), random.randrange(N)
    if kind == 'unif': return A, random.randrange(N)
hexkind = {'trans': 'trans', 'afh': 'aff', 'afall': 'aff', 'unif': 'unif'}[mode]
hopkind = {'trans': 'trans', 'afh': 'trans', 'afall': 'aff', 'unif': 'trans'}[mode]
with open(out, 'w') as f:
    f.write(f"{n} {n} {N} aff\n")
    for l in range(n):
        for p in lines[l]:
            a, b = mp(hexkind); f.write(f"{int(p)} {l} {a} {b}\n")
    for j in range(2):
        perm = list(range(n)); random.shuffle(perm)
        for p in range(n):
            a, b = mp(hopkind); f.write(f"{p} {perm[p]} {a} {b}\n")

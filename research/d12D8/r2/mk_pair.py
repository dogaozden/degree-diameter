"""Pair-design lift of "H(q) + 2 hops": group Z_5 (levels) x Z_f (fibre).
Hexagon edge of colour c (proper (q+1)-edge-colouring): level 0, fibre +C[c//2] if c even, -C[c//2] if c odd
(read point -> line; i.e. colour pairs form oriented 2-factors). Hop j (p -> M_j(p)): level j, fibre H[j-1].
usage: mk_pair.py q f Mvar seed "C0,C1,..." "H1,H2" out [colseed]
Mvar: rand | same | inc | incsame | inc1. If gcd(5,f)=1 the group is Z_5f via CRT, else a multiplication table."""
import sys, os, random, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
from math import gcd
q, f, var, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
C = [int(x) for x in sys.argv[5].split(',')]; H = [int(x) for x in sys.argv[6].split(',')]
out = sys.argv[7]; colseed = int(sys.argv[8]) if len(sys.argv) > 8 else 1
LV = int(os.environ.get('LV', 5))
random.seed(seed)
n, lines = load_hex(q)
col = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s{colseed}.npy'))
m = LV * f
cyc = gcd(LV, f) == 1
def enc(a, b):
    a %= LV; b %= f
    if cyc:
        for x in range(m):
            if x % LV == a and x % f == b: return x
    return a * f + b
pl = [[] for _ in range(n)]
for l in range(n):
    for p in lines[l]: pl[int(p)].append(l)
def rand_bij():
    perm = list(range(n)); random.shuffle(perm); return perm
def inc_matching(c):  # colour class c is a perfect matching point -> line
    M = [-1] * n
    for l in range(n):
        for k in range(q + 1):
            if col[l, k] == c: M[int(lines[l, k])] = l
    return M
if var == 'rand': M1, M2 = rand_bij(), rand_bij()
elif var == 'same': M1 = rand_bij(); M2 = M1
elif var == 'inc': M1, M2 = inc_matching(0), inc_matching(1)
elif var == 'incsame': M1 = inc_matching(0); M2 = M1
elif var == 'inc1': M1, M2 = inc_matching(0), rand_bij()
with open(out, 'w') as fo:
    fo.write(f"{n} {n} {m} {'cyc' if cyc else 'table'}\n")
    if not cyc:
        for g in range(m):
            a, b = divmod(g, f)
            fo.write(' '.join(str(((a + h // f) % LV) * f + (b + h % f) % f) for h in range(m)) + '\n')
    for l in range(n):
        for k in range(q + 1):
            c = int(col[l, k]); s = C[c // 2] if c % 2 == 0 else -C[c // 2]
            fo.write(f"{int(lines[l, k])} {l} {enc(0, s)}\n")
    for p in range(n):
        fo.write(f"{p} {M1[p]} {enc(1, H[0])}\n")
        fo.write(f"{p} {M2[p]} {enc(2, H[1])}\n")
print(out)

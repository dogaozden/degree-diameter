"""Class base for classcheck: H(q) edges classed by colour (0..q), hop1 class q+1, hop2 class q+2.
usage: mk_cls.py q Mvar seed out [colseed]   Mvar: rand | same | inc | incsame | inc1 | none (no hops)"""
import sys, os, random, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, var, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
colseed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
random.seed(seed)
n, lines = load_hex(q)
col = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s{colseed}.npy'))
def rand_bij():
    perm = list(range(n)); random.shuffle(perm); return perm
def inc_matching(c):
    M = [-1] * n
    for l in range(n):
        for k in range(q + 1):
            if col[l, k] == c: M[int(lines[l, k])] = l
    return M
M1 = M2 = None
if var == 'rand': M1, M2 = rand_bij(), rand_bij()
elif var == 'same': M1 = rand_bij(); M2 = M1
elif var == 'inc': M1, M2 = inc_matching(0), inc_matching(1)
elif var == 'incsame': M1 = inc_matching(0); M2 = M1
elif var == 'inc1': M1, M2 = inc_matching(0), rand_bij()
K = q + 3 if M1 else q + 1
with open(out, 'w') as fo:
    fo.write(f"{n} {n} {K}\n")
    for l in range(n):
        for k in range(q + 1):
            fo.write(f"{int(lines[l, k])} {l} {int(col[l, k])}\n")
    if M1:
        for p in range(n):
            fo.write(f"{p} {M1[p]} {q + 1}\n{p} {M2[p]} {q + 2}\n")

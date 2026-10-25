"""Star-product-type permutation lift for affcheck: H(q) edges of colour c carry x -> A[c]*x + B[c] (point->line),
hop edges: one bijection M (or two), each point p has hop edges to M1(p) with x -> x + h1 and to M2(p) with x -> x + h2.
usage: mk_star.py q N Mvar seed "A0,..,Aq" "B0,..,Bq" "h1,h2" out [colseed]   Mvar: rand | same | inc0 (M = colour-0 matching) | incsame"""
import sys, os, random, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, N, var, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
A = [int(x) for x in sys.argv[5].split(',')]; B = [int(x) for x in sys.argv[6].split(',')]
h = [int(x) for x in sys.argv[7].split(',')]; out = sys.argv[8]
colseed = int(sys.argv[9]) if len(sys.argv) > 9 else 1
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
if var == 'rand': M1, M2 = rand_bij(), rand_bij()
elif var == 'same': M1 = rand_bij(); M2 = M1
elif var == 'inc0': M1 = M2 = inc_matching(0)
elif var == 'inc01': M1, M2 = inc_matching(0), inc_matching(1)
with open(out, 'w') as f:
    f.write(f"{n} {n} {N} aff\n")
    for l in range(n):
        for k in range(q + 1):
            c = int(col[l, k]); f.write(f"{int(lines[l, k])} {l} {A[c] % N} {B[c] % N}\n")
    for p in range(n):
        f.write(f"{p} {M1[p]} 1 {h[0] % N}\n{p} {M2[p]} 1 {h[1] % N}\n")

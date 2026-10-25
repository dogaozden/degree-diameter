"""Random Z_m lift of Delorme's X_2 (5 levels) with level-DEPENDENT voltages. Base = X_2 itself:
points (p,i) -> id i*n+p, lines (l,i) -> id i*n+l. Hops: (p,i) ~ (M_j(p), i+j). usage: q Mvariant m seed out"""
import sys, random
from hexlib import load_hex
import importlib.util
q, var, m, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
random.seed(seed)
n, lines = load_hex(q)
def rand_bij():
    perm = list(range(n)); random.shuffle(perm); return perm
M1, M2 = rand_bij(), rand_bij()
if var == 'same': M2 = M1
with open(out, 'w') as f:
    f.write(f"{5*n} {5*n} {m} cyc\n")
    for i in range(5):
        for l in range(n):
            for p in lines[l]:
                f.write(f"{i*n+int(p)} {i*n+l} {random.randrange(m)}\n")
        for p in range(n):
            f.write(f"{i*n+p} {((i+1)%5)*n+M1[p]} {random.randrange(m)}\n")
            f.write(f"{i*n+p} {((i+2)%5)*n+M2[p]} {random.randrange(m)}\n")

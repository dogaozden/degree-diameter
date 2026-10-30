# Independent rebuild: regular voltage lift of the base [[2,3],[3,2]] (A0-B0 x2, A0-B1 x3, A1-B0 x3, A1-B1 x2)
# by a group given as a Cayley table; voltages from "SOL x X y Y1 Y2 z Z1 Z2 Z3 w W" (identity 0 completes each set).
import sys, random
tab = [list(map(int, l.split())) for l in open(sys.argv[1]).read().split('\n')[1:] if l.strip()]
n = len(tab); mul = lambda a, b: tab[a][b]
assert all(mul(0, a) == a == mul(a, 0) for a in range(n))
for _ in range(20000):   # spot-check associativity
    a, b, c = (random.randrange(n) for _ in range(3)); assert mul(mul(a, b), c) == mul(a, mul(b, c))
t = sys.argv[2].split(); x = int(t[2]); y = [int(t[4]), int(t[5])]; z = [int(t[7]), int(t[8]), int(t[9])]; w = int(t[11])
V = {('A0','B0'): [0, x], ('A0','B1'): [0] + y, ('A1','B0'): z, ('A1','B1'): [0, w]}
idx = {'A0': 0, 'A1': 1, 'B0': 2, 'B1': 3}
E = set()
for (a, b), gs in V.items():
    for g in gs:
        for h in range(n):
            E.add((idx[a] * n + h, idx[b] * n + mul(h, g)))
print(4 * n); [print(u, v) for u, v in sorted(E)]

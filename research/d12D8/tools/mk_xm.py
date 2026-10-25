"""Delorme's D=7 graph X(M) as a lift: hexagon edges voltage 0, k hop matchings with voltages 1..k in Z_(2k+1)."""
import sys, random
from hexlib import load_hex, write_base
q = int(sys.argv[1]); k = int(sys.argv[2]); m = int(sys.argv[3]) if len(sys.argv) > 3 else 2 * k + 1
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
out = sys.argv[5] if len(sys.argv) > 5 else f'/tmp/xm_q{q}_k{k}_m{m}.base'
random.seed(seed)
n, lines = load_hex(q)
E = []
for l in range(n):
    for p in lines[l]:
        E.append((int(p), l, 0))
for j in range(1, k + 1):
    perm = list(range(n)); random.shuffle(perm)
    for p in range(n):
        E.append((p, perm[p], j % m))
write_base(out, n, E, m)
print(out)

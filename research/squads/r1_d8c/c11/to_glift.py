"""to_glift.py: write a glift file (Z_{5K} lift, K coprime to 5 or not: CRT map Z_5 x Z_K -> Z_{5K} needs gcd(5,K)=1).
Usage: python3 to_glift.py BASE HEXFILE K OUT  (HEXFILE: lines 'u v h' from lift7; matchings from BASE)."""
import sys
from math import gcd
base, hexf, K, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
assert gcd(5, K) == 1
M = 5 * K
def crt(g1, g2):
    for x in range(M):
        if x % 5 == g1 and x % K == g2:
            return x
lines = open(base).read().split('\n')
V = int(lines[0])
N = V // 2
darts = []
hexv = {}
for ln in open(hexf):
    u, v, h = map(int, ln.split())
    hexv[(u, v)] = h
for ln in lines[1:]:
    if not ln.strip():
        continue
    t, u, v, c = map(int, ln.split())
    if t == 0:
        a = crt(0, hexv[(u, v)])
    else:
        a = crt(c, 0)
    darts.append((u, v, a))
with open(out, 'w') as f:
    f.write(f'Z {M}\n{V}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for u, v, a in darts:
        f.write(f'{u} {v} {a}\n')
print('wrote', out, 'darts', len(darts), 'M', M)

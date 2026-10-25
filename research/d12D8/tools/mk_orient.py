"""Hexagon-only (or + random hops) Z_m lift with voltages from an Eulerian orientation: colour classes 0..4 oriented
point->line (+1), 5..9 line->point (point->line traversal = -1). Optional: 'scaled' uses voltage c*s(colour)."""
import sys, random
from hexlib import load_hex, write_base
q, m, mode, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
random.seed(seed)
n, lines = load_hex(q)
col = {}
for row in open('/home/user/degree-diameter/research/squads/d12D8_r1/c3/col_s1.txt'):
    a = list(map(int, row.split()))
    l = a[0]
    for k, p in enumerate(lines[l]): col[(int(p), l)] = a[1 + k]
E = []
for l in range(n):
    for p in lines[l]:
        c = col[(int(p), l)]
        if mode == 'orient': g = 1 if c < 5 else m - 1
        elif mode == 'orient2': g = (1 if c < 5 else m - 1) * (1 + (c % 5)) % m   # weights 1..5 per class pair
        elif mode == 'rand': g = random.randrange(m)
        E.append((int(p), l, g))
write_base(out, n, E, m)

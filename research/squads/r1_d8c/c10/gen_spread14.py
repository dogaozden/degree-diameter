"""Z_m lift of H(5) with hexagon voltages from the Hermitian spread S and two point->line matchings.
usage: gen_spread.py m x1 x2 x3 mode seed OUT
 hex voltage of flag (p,l): x1*[l in S] + x2*[l not in S and p = s(l)] + x3*[p covered by S]
 s(l) = unique spread line meeting l (l not in S).
 mode 'rand': matchings phi1, phi2 uniform random bijections, voltages 1 and 2
 mode 'ident': phi2 = phi1 shifted by the spread-line map (point p -> line through p on the S-line structure)
"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import numpy as np
from hexlib import load
m, x1, x2, x3 = map(int, sys.argv[1:5]); mode = sys.argv[5]; seed = int(sys.argv[6]); out = sys.argv[7]
q = 5
N, LP, PL, coord = load(q)
S = np.load('/home/user/degree-diameter/research/squads/r1_d8c/c10/spread_lines.npy')
L = N
inS = np.zeros(L, bool); inS[S] = True
covered = np.zeros(N, bool); covered[LP[S].reshape(-1)] = True
# s(l): for l not in S, the spread line meeting l (in a point): S-lines through points of l
sline_of_point = {}
for a in S:
    for p in LP[a]:
        sline_of_point[p] = a
# line -> spread line meeting it: a point p of l on a spread line -> that spread line
s_of = np.full(L, -1)
for l in range(L):
    if inS[l]:
        continue
    for p in LP[l]:
        if covered[p]:
            s_of[l] = sline_of_point[p]
            break
rng = np.random.default_rng(seed)
rows = []
for l in range(L):
    for p in LP[l]:
        if inS[l]:
            v = x1
        elif covered[p]:
            v = x2 if sline_of_point.get(p) == s_of[l] else 0
        else:
            v = 0
        rows.append((p, N + l, (v + x3 * covered[p]) % m))
if mode == 'rand':
    phi1 = rng.permutation(N); phi2 = rng.permutation(N)
else:
    raise SystemExit('mode unknown')
for p in range(N):
    rows.append((p, N + phi1[p], 1 % m))
    rows.append((p, N + phi2[p], 4 % m))
with open(out, 'w') as f:
    f.write(f'Z {m}\n{2 * N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for r in rows:
        f.write('%d %d %d\n' % r)
print('wrote', out, 'rows', len(rows), 'lines in S', int(inS.sum()), 'covered pts', int(covered.sum()))

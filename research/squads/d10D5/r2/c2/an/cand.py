# candidate 9th flags for the k=8 set of r1/c5 (k8b.sol): collinear freed points / concurrent freed lines counts
import struct, sys, itertools
from collections import Counter
GQ = '/home/user/degree-diameter/research/squads/d10D5/r2/c2/gq/gq_q7.bin'
SOL = '/home/user/degree-diameter/research/squads/d10D5/r1/c5/k8b.sol'
with open(GQ, 'rb') as f:
    q, N, _ = struct.unpack('<3i', f.read(12))
    Q1 = q + 1
    pts = struct.unpack('<%di' % (N * Q1), f.read(4 * N * Q1))
lines = [set(pts[l * Q1:(l + 1) * Q1]) for l in range(N)]
lof = [[] for _ in range(N)]
for l in range(N):
    for p in lines[l]: lof[p].append(l)
L = [ln.split() for ln in open(SOL) if ln.strip()]
sig = list(map(int, L[2])); assert len(sig) == N and L[3] == L[2]
F = [266, 41, 225, 65, 263, 283, 398, 253]
FL = [sig[p] for p in F]
print('freed points', F, 'freed lines', FL)
print('flags check', [(p, sig[p]) for p in F])
def col(a, b):  # collinear points (distinct): share a line
    return a != b and any(b in lines[l] for l in lof[a])
def conc(l, m):
    return l != m and len(lines[l] & lines[m]) == 1
cp = sum(1 for a, b in itertools.combinations(F, 2) if col(a, b))
cl = sum(1 for a, b in itertools.combinations(FL, 2) if conc(a, b))
print('collinear freed point pairs', cp, 'of 28; concurrent freed line pairs', cl, 'of 28')
best = []
for p in range(N):
    if p in F: continue
    for l in lof[p]:
        if l in FL: continue
        c1 = sum(1 for f in F if col(f, p))
        c2 = sum(1 for m in FL if conc(m, l))
        best.append((c1 + c2, c1, c2, p, l))
best.sort(reverse=True)
print('candidates total', len(best))
print('histogram of c1+c2', sorted(Counter(b[0] for b in best).items(), reverse=True)[:12])
for b in best[:40]: print('score', b[0], 'coll_pts', b[1], 'conc_lines', b[2], 'flag', f'{b[3]}:{b[4]}')

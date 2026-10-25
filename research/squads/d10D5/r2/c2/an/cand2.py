# for the 8 freed flags of base8: score candidate 9th flags by (collinear freed pts c1, concurrent freed lines c2,
# and x = number of old freed flags i with BOTH point collinear and line concurrent with the new flag = pairs needing no hub link)
import struct, itertools
GQ = '/home/user/degree-diameter/research/squads/d10D5/r2/c2/gq/gq_q7.bin'
with open(GQ, 'rb') as f:
    q, N, _ = struct.unpack('<3i', f.read(12)); Q1 = q + 1
    pts = struct.unpack('<%di' % (N * Q1), f.read(4 * N * Q1))
lines = [set(pts[l * Q1:(l + 1) * Q1]) for l in range(N)]
lof = [[] for _ in range(N)]
for l in range(N):
    for p in lines[l]: lof[p].append(l)
L = [ln.split() for ln in open('/home/user/degree-diameter/research/squads/d10D5/r2/c2/base8.lift2.sol') if ln.strip()]
sig = list(map(int, L[2]))
F = [266, 41, 225, 65, 263, 283, 398, 253]; FL = [sig[p] for p in F]
def col(a, b): return a != b and any(b in lines[l] for l in lof[a])
def conc(l, m): return l != m and len(lines[l] & lines[m]) == 1
rows = []
for p in range(N):
    if p in F: continue
    for l in lof[p]:
        if l in FL: continue
        c1 = sum(1 for f in F if col(f, p)); c2 = sum(1 for m in FL if conc(m, l))
        both = sum(1 for f, m in zip(F, FL) if col(f, p) and conc(m, l))
        rows.append((c1, c2, both, p, l))
print('old pairs both-nothing:', sum(1 for a, b in itertools.combinations(range(8), 2) if col(F[a], F[b]) and conc(FL[a], FL[b])))
sel = [r for r in rows if r[0] <= 1 and r[1] >= 3]
sel.sort(key=lambda r: (-(r[1]), r[0], -r[2]))
print('candidates with c1<=1 and c2>=3:', len(sel))
for r in sel[:25]: print('c1', r[0], 'c2', r[1], 'both', r[2], 'flag', f'{r[3]}:{r[4]}')

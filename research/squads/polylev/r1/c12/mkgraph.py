import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
q, N, L = H.q, H.N, H.L
print('q', q, 'N', N, 'L', L, flush=True)
# points graph: collinear points
pn = [set() for _ in range(N)]
for l in range(L):
    pts = H.lines[l]
    for p in pts:
        for r in pts:
            if r != p:
                pn[p].add(int(r))
# lines graph: lines meeting
ln = [set() for _ in range(L)]
for p in range(N):
    ls = H.PL[p]
    for a in ls:
        for b in ls:
            if a != b:
                ln[a].add(int(b))
degs = set(len(s) for s in pn) | set(len(s) for s in ln)
print('degrees', degs, flush=True)
D = max(degs)
assert len(set(len(s) for s in pn)) == 1 and len(set(len(s) for s in ln)) == 1
A = np.array([sorted(s) for s in pn], dtype=np.int32)
A.tofile('points_adj.bin')
B = np.array([sorted(s) for s in ln], dtype=np.int32)
B.tofile('lines_adj.bin')
np.array([N, L, D], dtype=np.int32).tofile('dims.bin')
print('written', A.shape, B.shape, flush=True)

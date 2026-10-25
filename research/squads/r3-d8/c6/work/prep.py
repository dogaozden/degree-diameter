"""Prepare c6 inputs: H(3) in lanneal format, dualities checked, hop matchings for variants A, B, C."""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh

W = '/home/user/degree-diameter/research/squads/r3-d8/c6/work'
Q = 3
H = gh.load(Q)
N = H.N
print('N', N, 'lines per point check', np.bincount(np.array([int(p) for k in range(N) for p in H.lines[k]]), minlength=N).min(),
      np.bincount(np.array([int(p) for k in range(N) for p in H.lines[k]]), minlength=N).max())
with open(os.path.join(W, 'h3.txt'), 'w') as fh:
    fh.write(f'{Q} {N}\n')
    for k in range(N):
        fh.write(' '.join(str(int(p)) for p in H.lines[k]) + '\n')

D, adj = gh.distances(H)
D = D.astype(np.int64)
H_nb = [set() for _ in range(N)]  # line indices incident to point p
for k in range(N):
    for p in H.lines[k]:
        H_nb[int(p)].add(k)

duals = []
for i in range(1, 5):
    phi = np.load(f'/home/user/degree-diameter/research/squads/r2-d8/d7/dual_q3_s{i}.npy').astype(np.int64)
    bij = len(set(phi.tolist())) == 2 * N
    dp = bool((D[np.ix_(phi, phi)] == D).all())
    pts_to_lines = bool((phi[:N] >= N).all())
    absolute = int(sum(1 for p in range(N) if D[p, phi[p]] == 1))
    s = phi[:N] - N
    flag_hits = sum(1 for p in range(N) if s[p] in H_nb[p])
    print(f'dual s{i}: bijection {bij} distance_preserving {dp} points->lines {pts_to_lines} absolute {absolute} flag_hits {flag_hits}')
    duals.append(s)

print('pairwise collisions (same point-line pair) and flag overlaps:')
for i in range(4):
    for j in range(i + 1, 4):
        coll = int((duals[i] == duals[j]).sum())
        print(f'  s{i+1} s{j+1}: shared pairs {coll}')
np.save(os.path.join(W, 'duals_points.npy'), np.array(duals))

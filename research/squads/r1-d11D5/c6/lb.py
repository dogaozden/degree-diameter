# Independent 4-cycle check (codegree formula) and an exact lower bound on far pairs for ANY
# regular lift by a group H of order k: far >= sum over ordered (x,y) of max(0, k - #NB walks of length <= L).
import json, numpy as np, sys
from collections import Counter
k = int(sys.argv[1]) if len(sys.argv) > 1 else 4
d = json.load(open('/home/user/degree-diameter/research/gq4x/graphs/as_w2_q9_n1782.json'))
E = d['output'][1]; n = 1782
A = np.zeros((n, n))
for u, v in E:
    A[u, v] = 1; A[v, u] = 1
side = np.load('side.npy').astype(int)
deg = A.sum(1); D = np.diag(deg); I = np.eye(n)
C2 = A @ A                                    # common-neighbour counts (diagonal = degree)
off = ~np.eye(n, dtype=bool)
c4 = (np.where(off, C2, 0) * (np.where(off, C2, 0) - 1) / 2).sum(1)   # 4-cycles through x = sum_c binom(codeg,2)
W4diag_check = np.round(np.diag(A @ (A @ (A @ A - D) - (D - I) @ A) - (D - I) @ (A @ A - D))).astype(int)
print('4-cycles per vertex via codegree: distribution', Counter(c4.astype(int).tolist()))
print('closed NB 4-walks = 2*C4 agrees:', bool(np.all(W4diag_check == 2 * c4.astype(int))))
print('vertices on NO 4-cycle:', int((c4 == 0).sum()))
W2 = A @ A - D
W4 = A @ (A @ W2 - (D - I) @ A) - (D - I) @ W2
same = side[:, None] == side[None, :]
dist_ok = np.load('dist.npy').astype(int)
# same-side ordered pairs x != y: walks of length <= 4 are W2 + W4; distance-4 pairs have W2 = 0
walks = W2 + W4
mask = same & off
lb_pairs = np.maximum(0, k - np.round(walks[mask]).astype(int))
lb_diag = np.maximum(0, (k - 1) - np.round(np.diag(W4)).astype(int))   # x = y: trivial walk covers 0
print(f'k={k}: LB same-side pairs (ordered) = {int(lb_pairs.sum())}  pairs with <k walks: {int((lb_pairs>0).sum())}')
print('   distribution of (walk count) over same-side d=2 pairs with <k walks:',
      Counter(np.round(walks[mask & (dist_ok == 2)]).astype(int)[np.round(walks[mask & (dist_ok == 2)]).astype(int) < k].tolist()))
print(f'k={k}: LB diagonal (x=y) = {int(lb_diag.sum())}')
# cross-side pairs: odd walks of length <= 5
W3 = A @ W2 - (D - I) @ A
W5 = A @ W4 - (D - I) @ W3
cw = np.round(W3 + W5 + A).astype(int)  # length 1,3,5 walks
cmask = (~same)
lb_cross = np.maximum(0, k - cw[cmask])
print(f'k={k}: LB cross-side (ordered) = {int(lb_cross.sum())}  min #walks over cross pairs = {int(cw[cmask].min())}')
LB = int(lb_pairs.sum()) + int(lb_diag.sum()) + int(lb_cross.sum())
print(f'LOWER BOUND on far pairs for any regular lift by a group of order {k}: {LB}')
np.save('c4.npy', c4.astype(np.int32))

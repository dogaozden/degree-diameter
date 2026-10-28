"""q=3: all 4-element 4-dominating line sets containing line 0 (every 4-set of lines hitting every 4-ball).
A set S dominates iff every line L has S & Ball4(L) nonempty. Transitivity of G2(3) on lines makes this WLOG."""
import sys, time, itertools
import numpy as np
from common import *
q = 3
H = load(q)
B = ball_matrix_cached(H, q)
Lc = H.L
bits = [int(''.join('1' if B[l, m] else '0' for m in range(Lc)[::-1]), 2) for l in range(Lc)]  # ball(L) as int
FULL = (1 << Lc) - 1
# unhit-set bitmask: bit L set iff L's ball is not hit yet. Ball contains M iff B[L,M].
colmask = [int(''.join('1' if B[l, m] else '0' for l in range(Lc)[::-1]), 2) for m in range(Lc)]  # bit l set iff M in ball(l)
t = time.time()
def pencil_point(S):
    common = set(H.lines[S[0]].tolist())
    for m in S[1:]:
        common &= set(H.lines[m].tolist())
    return common
sols = []
def rec(S, unhit, depth):
    if unhit == 0:
        sols.append(tuple(S)); return
    if depth == 0:
        return
    # branch on the lowest unhit line L: some M in ball(L) must be added
    low = (unhit & -unhit).bit_length() - 1
    for m in np.nonzero(B[low])[0]:
        m = int(m)
        rec(S + [m], unhit & ~colmask[m], depth - 1)
M0 = 0
unhit0 = FULL & ~colmask[M0]
rec([M0], unhit0, 3)
print('q=3: dominating 4-sets containing line 0 (with repeats):', len(sols), 'time', round(time.time() - t, 1))
uniq = sorted(set(tuple(sorted(s)) for s in sols))
print('distinct:', len(uniq))
nonpen = [s for s in uniq if len(pencil_point(list(s))) == 0]
print('non-pencil 4-dominating sets containing line 0:', len(nonpen))
for s in nonpen[:10]:
    print(s, [H.lines[m].tolist() for m in s])
np.save('q3_nonpencil_containing0.npy', np.array(nonpen, dtype=np.int64) if nonpen else np.zeros((0, 4), dtype=np.int64))

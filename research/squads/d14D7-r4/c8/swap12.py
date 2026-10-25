# c8: (1,2)-swap check on a partial ovoid S: a point y in S is replaced by two non-orthogonal points x1, x2
# whose only conflict in S is y. Also reports maximality and the 1-tight counts.
import sys
from collections import defaultdict
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O
from union240 import load_flags

if __name__ == '__main__':
    S = load_flags(sys.argv[1])
    inS = np.zeros(O.N, dtype=bool); inS[S] = True
    Z = (O.Bm(O.U, O.U[S]) == 0)            # (N, |S|): orthogonal to y in S
    Z[S, np.arange(len(S))] = False         # a point is not a conflict of itself
    cnt = Z.sum(axis=1)
    out = np.nonzero((~inS) & (cnt == 0))[0]
    print("|S|", len(S), "addable (maximal if 0):", len(out))
    print("1-tight outside points:", int(((~inS) & (cnt == 1)).sum()), " 2-tight:", int(((~inS) & (cnt == 2)).sum()))
    groups = defaultdict(list)
    for x in np.nonzero((~inS) & (cnt == 1))[0]:
        y = int(np.nonzero(Z[x])[0][0])
        groups[y].append(int(x))
    found = 0
    for yi, xs in groups.items():
        if len(xs) < 2: continue
        xs = np.array(xs)
        b = O.Bm(O.U[xs], O.U[xs])
        for a in range(len(xs)):
            for c in range(a + 1, len(xs)):
                if b[a, c] != 0:
                    found += 1
                    if found <= 3: print("(1,2)-swap: remove", S[yi], "add", xs[a], xs[c])
    print("(1,2)-swaps found:", found)

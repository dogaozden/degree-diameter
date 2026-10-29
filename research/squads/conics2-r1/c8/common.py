import sys, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load
D = '/home/user/degree-diameter/research/squads/conics2-r1/data'

def setup(q):
    q, N, LP, PL, X = load(f'{D}/hex_q{q}.bin')
    # collinearity: col[p] = points sharing a line with p (excluding p)
    col = []
    for p in range(N):
        s = set()
        for l in PL[p]:
            s.update(LP[l].tolist())
        s.discard(p)
        col.append(s)
    # distance<=2 conflict sets (closed neighbourhoods intersect)
    conf = []
    for p in range(N):
        s = set(col[p])
        for x in col[p]:
            s |= col[x]
        s.discard(p)
        conf.append(sorted(s))
    return q, N, LP, PL, col, conf

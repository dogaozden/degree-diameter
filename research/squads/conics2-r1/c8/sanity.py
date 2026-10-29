from common import *
for q in (2,3,4,5):
    q,N,LP,PL,col,conf = setup(q)
    print(q, N, set(len(c) for c in col), set(len(c) for c in conf), 'opp deg', N-1-len(conf[0]))

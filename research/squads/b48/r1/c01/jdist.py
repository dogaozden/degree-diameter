import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r1/c01')
from mgrp import Meta
from walks import walks
from collections import Counter
G=Meta(55,20,2)
def report(S,label=""):
    # number of walks (not distinct) per depth and per j-class for odd depths
    W=None
    import walks as w
    from collections import defaultdict
    # count walks by (endpoint j) for each depth
    cur={(0,-1):1}; jc=[Counter() for _ in range(9)]
    for d in range(1,8):
        nxt=defaultdict(int)
        for (g,last),c in cur.items():
            for li,s in enumerate(S):
                if li==last: continue
                nxt[(G.mul(g,s) if d%2 else G.mul(g,G.inv(s)),li)]+=c
        cur=nxt
        for (g,last),c in cur.items(): jc[d][g//55]+=c
    return jc
S=[0,929,1084,684]
jc=report(S)
for d in (1,3,5,7):
    print("depth",d,"walks per j-class:",[jc[d][j] for j in range(20)])
W=walks(S,8,G.mul,G.inv)
# distinct per j-class (odd depths <=7), and walks per j-class in total
odd=set()
for d in (1,3,5,7): odd|=set(W[d-1].keys())
print("distinct per j class (odd <=7):",[sum(1 for g in odd if g//55==j) for j in range(20)])

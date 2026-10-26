# count non-backtracking walks of length d from A-identity in the lift (dipole Haar graph), by endpoint
import sys
from collections import defaultdict
def walks(S, maxd, mul, inv):
    # states: (group element on current side, last label index). side alternates; start A-side at e, no last label
    # A-side vertex p: step via s -> B-side p*s (label s). B-side q: step via t^{-1}: A-side q*t^{-1}, label t, t != last label
    res=[]
    cur={(0,-1):1}   # A-side, identity
    for d in range(1,maxd+1):
        nxt=defaultdict(int)
        side_is_A = (d%2==1)
        for (g,last),c in cur.items():
            for li,s in enumerate(S):
                if li==last: continue
                if side_is_A: nxt[(mul(g,s),li)]+=c       # A -> B
                else: nxt[(mul(g,inv(s)),li)]+=c           # B -> A
        cur=nxt
        cnt=defaultdict(int)
        for (g,last),c in cur.items(): cnt[g]+=c
        res.append(cnt)
    return res  # res[d-1][g] = number of walks of length d ending at element g on side (B if d odd else A)

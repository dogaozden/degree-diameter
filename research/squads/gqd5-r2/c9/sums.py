# Achievable balanced sizes from cliques of PG(2,s) cores (delta=8), with per-core partner caps.
import itertools
N = {2:7, 3:13, 4:21, 5:31}
# partner cap (max number of other cores a core of order s can be joined to, heuristic arc bounds)
CAP = {5:6, 4:9, 3:13, 2:11}
best = {}
def rec(i, parts, total):
    pass
res = {}
sizes = [5,4,3,2]
for a in range(0,4):
  for b in range(0,6):
    for c in range(0,8):
      for d in range(0,10):
        m = a+b+c+d
        if m == 0: continue
        if a>0 and m-1 > CAP[5]: continue
        if b>0 and m-1 > CAP[4]: continue
        if c>0 and m-1 > CAP[3]: continue
        if d>0 and m-1 > CAP[2]: continue
        K = a*31+b*21+c*13+d*7
        res.setdefault(K, (a,b,c,d))
Ks = sorted(res)
M = 0
while M+1 in res or M+1 <= 93: M += 1
print("covered up to", M)
gaps = [k for k in range(7, 260) if k not in res and k>93]
print("first sums above 93 not representable:", gaps[:30])
print({k:res[k] for k in range(94,140) if k in res})

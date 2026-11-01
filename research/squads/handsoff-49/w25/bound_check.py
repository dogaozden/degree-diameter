# bound_check.py: |4D| for D = S^-1 S in Z^3 with S = {0, s1, s2, s3} (additive), i.e. the abelian-quotient bound of w20.
from itertools import product
gens = [(1,0,0),(0,1,0),(0,0,1)]
S = [(0,0,0)] + gens
D = set()
for a in S:
    for b in S:
        D.add(tuple(b[i]-a[i] for i in range(3)))
print("|D| =", len(D))
R = {(0,0,0)}
sizes = []
for step in range(1, 5):
    R = {tuple(r[i]+d[i] for i in range(3)) for r in R for d in D}
    sizes.append(len(R))
print("|kD| for k=1..4:", sizes)

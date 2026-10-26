import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r1/c01')
from mgrp import Meta
from walks import walks
G=Meta(55,20,2)
S=[0,929,1084,684]
print("S coords",[G.coord(x) for x in S])
W=walks(S,8,G.mul,G.inv)
for d in range(1,9):
    cov=len(W[d-1]); print("depth",d,"distinct",cov,"walks",sum(W[d-1].values()))
odd=set(); even=set()
for d in range(1,9):
    (odd if d%2 else even).update(W[d-1].keys())
print("B-side covered by len<=7 odd:",len(odd), "of",G.N)
print("A-side covered by len<=8 even (incl identity):",len(even|{0}), "of",G.N)
miss=[g for g in range(G.N) if g not in odd]
print("B-side uncovered", [(G.coord(g)) for g in miss])
print("j-class sizes covered on B:", [sum(1 for g in odd if g//55==j) for j in range(20)])
print("walk multiplicity for 64 (9,1):", [W[d].get(64,0) for d in range(8)])

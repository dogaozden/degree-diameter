import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4
G = Q4(5)
d = json.load(open(sys.argv[1]))
R, M = d['R'], d['M']
print('R', R, 'pairwise dpp', [[int(G.dpp[a,b]) for b in R] for a in R])
for x in R:
    print(x, 'M(x)=', M[x], 'M(R)', [M[y] for y in R], 'dll(M(x),M(y))', [int(G.dll[M[x],M[y]]) for y in R])

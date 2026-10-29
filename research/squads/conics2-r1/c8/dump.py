import sys
from common import *
q = int(sys.argv[1])
q, N, LP, PL, col, conf = setup(q)
with open(f'/home/user/degree-diameter/research/squads/conics2-r1/c8/geom_q{q}.txt', 'w') as f:
    f.write(f'{q} {N} {LP.shape[0]}\n')
    for l in range(LP.shape[0]):
        f.write(' '.join(map(str, LP[l])) + '\n')
print('ok')

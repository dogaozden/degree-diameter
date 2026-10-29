# expand a set of centres into G = all lines through each centre; write as line-index file
import sys
from common import *
q = int(sys.argv[1]); cent = np.load(sys.argv[2]); out = sys.argv[3]
q, N, LP, PL, col, conf = setup(q)
G = sorted(set(int(l) for o in cent for l in PL[o]))
open(out, 'w').write(' '.join(map(str, G)) + '\n')
print('centres', len(cent), 'lines', len(G))

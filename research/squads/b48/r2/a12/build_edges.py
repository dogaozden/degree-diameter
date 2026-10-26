# Haar graph H(G,S): (0,g) ~ (1, g*s) for s in S, vertices g (side A) and N+g (side B); N = 1120.
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r2/a12')
from common import load, N
MT = load()
S = list(map(int, sys.argv[1].split(',')))
assert S[0] == 0 and len(set(S)) == 4
out = open(sys.argv[2], 'w')
E = [(g, N + int(MT[g, s])) for g in range(N) for s in S]
out.write('%d\n' % (2 * N))
out.write(''.join('%d %d\n' % e for e in E))

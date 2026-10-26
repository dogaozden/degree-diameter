import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import *
print('G', G.name, NP, NL, 'lines per point', G.t+1)
n, E = graph()
print('base (no freed, no hubs):', bad(n, E), apsp_valid(n, E))

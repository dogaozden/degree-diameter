"""write best.edges for a freed line set R0 (no hubs, no other freed sets) and verify with apsp"""
import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from hubgraph import *
import subprocess
S = [int(x) for x in np.load(sys.argv[1])]
assert not G.con[np.ix_(S, S)].any(), 'not a partial spread'
n, E, deg = build_graph(S, [], [], [], [])
write('best.edges', n, E)
out = subprocess.run(['/home/user/degree-diameter/research/theorems/d5gq/apsp', 'best.edges', '7', '5'], capture_output=True, text=True).stdout.strip().splitlines()
print(len(S), out[-1], 'n', n)

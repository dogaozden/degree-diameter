"""Dump a saved state to an edge file and check it with the all-pairs BFS checker. Usage: verify.py state.pkl out.edges"""
import sys, pickle, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
st = pickle.load(open(sys.argv[1], 'rb'))
G = gqlib.Q4(5); g = Graph(G, st['r'])
eu, ev = g.edges(st['M'], st['R'])
write_edges(sys.argv[2], g.n, eu, ev)
deg = np.bincount(np.concatenate([eu, ev]), minlength=g.n)
print('n', g.n, 'edges', len(eu), 'maxdeg', deg.max(), 'mindeg', deg.min(), 'python bad', g.bad(st['M'], st['R']))
out = subprocess.run(['/home/user/degree-diameter/research/theorems/d5gq/apsp', sys.argv[2], str(st['r'] + 6), '5'], capture_output=True, text=True).stdout
print(out.strip())

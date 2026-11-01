"""w17: far counts (distance > 9) from one root per orbit of a mixed graph: python3 farorb.py FILE 0,630,... (offsets)"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w17')
from levels import load, levels
n, adj = load(sys.argv[1])
roots = [int(x) for x in sys.argv[2].split(',')]
for r in roots:
    c = levels(adj, r, maxd=9)
    print("root", r, "far(>9)=", n - sum(c))

import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4
import repair
G = Q4(5)
d = json.load(open(sys.argv[1]))
M, R = d['M'], d['R']
ok = repair.exact_conditions(G, 'H', 'H', M, R)
print(len(R), ok[0], ok[1][:3], repair.brute_bad(G, 'H', 'H', M, R))

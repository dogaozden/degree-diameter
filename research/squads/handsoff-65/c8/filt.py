import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from g2grp import *
from lin import preserves_phi
E = load_root_elems()
good = []
for e in E:
    u = unip(e)
    if preserves_phi(u): good.append(e)
print("total", len(E), "good unipotent", len(good))
pickle.dump(good, open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'wb'))

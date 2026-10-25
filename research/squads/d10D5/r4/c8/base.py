import sys, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import lns, numpy as np
S = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S['F']; sig = S['sig']; H = S['hubadj']
print('F', F)
print('sig of F', [int(sig[p]) for p in F])
c, unc = lns.cover(F, sig, H, listing=True)
print('cost', c, unc)

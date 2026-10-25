import sys, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4/c8')
import relax, lns, numpy as np
S0 = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S0['F']; sig = S0['sig']; H = S0['hubadj']
S = relax.linear_S(F, sig)
os.environ['FIX'] = '1'
new, info = relax.model(F, sig, H, S, [(3, 0)], secs=20, workers=1, seed=1, hint=True)
print('fixed-at-current model:', info)

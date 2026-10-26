import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4/c8')
import relax, lns, numpy as np
from ortools.sat.python import cp_model
S0 = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S0['F']; sig = S0['sig']; H = S0['hubadj']
S = relax.linear_S(F, sig)[:0] or relax.linear_S(F, sig)
print('lin', len(S))
# fix sigma to current assignment and check the objective equals the cover count
import types
orig = cp_model.CpModel
new, info = relax.model(F, sig, H, S, [(3, 0)], secs=20, workers=1, seed=1, hint=True)
print('model with hint:', info)
print('exact after:', relax.cover_sub(F, new, H, [(3, 0)])[0] if new is not None else None)
print('exact at hint:', relax.cover_sub(F, sig, H, [(3, 0)])[0])

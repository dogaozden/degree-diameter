# orbits of the full parabolic S-stabiliser H1 and of its subgroups: sizes and relaxed-orbit counts
import sys, numpy as np, collections
sys.argv = ['x', '/home/user/degree-diameter/research/squads/gqd5-r3/c1/H1.npy']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c1')
import orbsat2 as O
H = O.H
print('group order', len(H))
orbs = O.orbits_of(list(H))
print('H1 orbit sizes', collections.Counter(len(o) for o in orbs))
print('relaxed orbits', [len(o) for o in orbs if O.relaxed(o)])

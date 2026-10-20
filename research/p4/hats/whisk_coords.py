"""Print the symmetric whisker solution in coordinates: for each chosen orbit, a representative S-point X and
whisker w (as X plus the other points of w).  python3 whisk_coords.py q"""
import json
import sys

from g2_gens import Hex

q = int(sys.argv[1])
d = json.load(open(f'whiskers_sym2_q{q}.json'))
H = Hex(q)
P, lines = H.P, H.lines
S, v = d['S'], d['v']
print('hyperplane', d['hyperplane'], ' v =', [P[p] for p in lines[v]])
Sline_of = {p: s for s in S for p in lines[s]}
for o in d['orbits_chosen'][:12]:
    X, k = o[0]
    others = [P[p] for p in lines[k] if p != X]
    print('X', P[X], ' S-line', [P[p] for p in lines[Sline_of[X]]][:2], ' whisker other pts', others[:2])

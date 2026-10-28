import sys, itertools, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c16')
import gen_c16 as g
from screen import score
out = []
def rec(label, args, group='psl'):
    m, rows = score(args, group=group)
    out.append((m, label))
    print(label, m, flush=True)
# Kloosterman-type, Delta 6, 7, 8 (no symmetry), small integer sets
for A in ['1,2,3,4,5,6', '-3,-2,-1,1,2,3', '0,1,2,3,4,5', '-2,-1,0,1,2,3', '3,4,5,6,7,8', '2,3,4,5,6,7']:
    rec('kloos6 ' + A, ['kloos', A, '{q}'])
rec('kloos7 -3..3', ['kloos', '-3,-2,-1,0,1,2,3', '{q}'])
rec('kloos8 -4..3', ['kloos', '-4,-3,-2,-1,0,1,2,3', '{q}'])
# continuant words of length 2, Delta 6
for P in ['1:1,1:2,1:3,2:1,2:2,2:3', '1:2,2:1,1:3,3:1,2:3,3:2', '1:1,1:-1,2:1,2:-1,3:1,3:-1', '3:3,3:4,4:3,4:4,2:5,5:2']:
    rec('cont6 ' + P, ['cont', P, '{q}'])
# Cayley set without symmetry, 6 random small orbits-free elements
R = random.Random(1)
trip = [t for t in itertools.product(range(-2, 3), repeat=3) if t != (0,0,0) and t[0]*t[0]+t[1]*t[2] != 1]
for s in range(4):
    pick = R.sample(trip, 6)
    rec('cayno6 seed%d' % s, ['cayno'] + [','.join(map(str, t)) for t in pick] + ['{q}'])

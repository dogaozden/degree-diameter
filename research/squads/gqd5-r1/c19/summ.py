import sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
G = gqlib.Q4(5); D5 = repair.full_dist(G)
for f in sys.argv[1:]:
    st = pickle.load(open(f, 'rb')); r = st['r']; g = Graph(G, r)
    t0 = st['t0']; R = st['R'][t0]; Mt = st['M'][t0]
    two = repair.brute_bad(G, 'H', 'H', Mt, R, D5)
    ok, fails = repair.exact_conditions(G, 'H', 'H', Mt, R)
    print(f.split('/')[-1], 'r=%d s=%d' % (r, len(R)), 'whole_bad_after_anneal=%d' % g.bad(st['M'], st['R']),
          'two_level_bad=%d' % two, 'E1-E3 hold=%s' % ok, 'fails=%s' % sorted(set(f[0] for f in fails)))

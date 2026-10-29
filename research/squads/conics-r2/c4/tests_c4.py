# Driver for card c4: tests of CONICS.md sections 0-1 at prime q. Usage: python3 tests_c4.py Q
import sys, itertools
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run

q = int(sys.argv[1])
E = run(q)
P, idx, A, ell, Z, Zp = E['P'], E['idx'], E['A'], E['ell'], E['Z'], E['Zp']
build, is_pol, diam, degs, adj = E['build'], E['is_polarity'], E['diameter'], E['degs'], E['adjacency']
th_pt, th_ln, on_conic, cross, inc, nrm = E['th_pt'], E['th_ln'], E['on_conic'], E['cross'], E['inc'], E['nrm']
ell_pts = E['ell_pts']
SIG = {0: 'c', 'c': 1, 1: 0}          # sigma: 0->c->1->0 (four hats)
SIG_T = {0: 'c', 'c': 1, 1: 0}
out = []
def say(*a):
    s = ' '.join(str(x) for x in a); out.append(s); print(s)

# ---- conic frame: X_a=Z, X_c=Z', X_0=(1,0,u), X_1=(1,0,-u)
def frame4(u):
    X0 = idx[nrm((1, 0, u))]; X1 = idx[nrm((1, 0, -u))]
    return {'a': Z, 'c': Zp, 0: X0, 1: X1}
def frame3(u):
    X0 = idx[nrm((1, 0, u))]; X1 = idx[nrm((1, 0, -u))]
    return {'a': Z, 0: X0, 1: X1}

PI4 = {0: 'c', 'c': 1, 1: 0}; RHO4 = {0: 'c', 'c': 1, 1: 0}
PI3 = {0: 1, 1: 0}; RHO3 = {0: 0, 1: 1}
T4 = [0, 'c', 1]; T3 = [0, 1]

say('== q=%d ==' % q)
# Lemma 1.3 / Thm 1.4 and Cor 1.7 on conic frames
for u in range(1, q):
    for name, fr, T, pi, rho in [('3hat', frame3(u), T3, PI3, RHO3), ('4hat', frame4(u), T4, PI4, RHO4)]:
        r = build(fr, 'a', T, pi, rho)
        I, tau, S = r
        pol = is_pol(I, tau)
        pts, lns = E['elements'](I)
        dg = degs(I)
        D = diam(I)
        nP = len([x for x in pts if x[0] in ('P', 'Q', 'H')])
        nL = len([x for x in lns if x[0] in ('L', 'M', 'K')])
        say(name, 'u=%d' % u, 'tau=', tau, 'polarity=', pol, 'points', nP, 'lines', nL, 'diam', D,
            'maxdeg', max(dg.values()), 'mindeg', min(dg.values()))

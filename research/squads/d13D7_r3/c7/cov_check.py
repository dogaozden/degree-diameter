import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r3/c7')
from common import *
coord, code = load_hex()
D = directions()
def read_offsets(path):
    V = []
    for line in open(path):
        t = line.split()
        if not t or t[0].startswith('#'): continue
        a, b, c, e, f = [int(z) for z in t[:5]]
        V.append(((e + 2 * a) % Q, b % Q, c % Q, f % Q))  # coset (s,b,c,f)
    return V
def cov(V):
    V = np.array(V)
    c = 0
    for n in D:
        vals = set(((n[0]*V[:,0] + n[1]*V[:,1] + n[2]*V[:,2] + n[3]*V[:,3]) % Q).tolist())
        c += (len(vals) == Q)
    return c
def compatible_dirs(V):
    pts = []
    for v in V:
        pts += coset_lift_points(*v)
    P = np.array(pts)
    e4 = np.array([0,0,0,0,1,0,0])
    S0 = coord[(coord[:,0] == 0)]
    S0 = S0[[not np.array_equal(x, e4) and (x[5]-2*x[1]) % Q == 0 for x in S0]]
    ok = []
    for x in S0:
        Bv = (x[0]*P[:,4] + x[4]*P[:,0] + x[1]*P[:,5] + x[5]*P[:,1] + x[2]*P[:,6] + x[6]*P[:,2] - 2*x[3]*P[:,3]) % Q
        if (Bv != 0).all(): ok.append(x)
    dirs = set()
    for x in ok:
        dirs.add(tuple(normalize(np.array([x[1], x[6], (-2*x[3]) % Q, x[2]]))))
    return len(ok), len(dirs)
V = read_offsets(sys.argv[1]) if len(sys.argv) > 1 else read_offsets('/home/user/degree-diameter/research/d13D7/sets/R320_offsets29_u1-0-0-9-0.txt')
print('cosets', len(V), 'distinct', len(set(V)))
c = cov(V)
n_comp, n_dir = compatible_dirs(V)
print('cov =', c, '  122-cov =', 122 - c, '  compatible points at infinity =', n_comp, ' distinct directions =', n_dir)
print('score 11|K|+|I| =', 11*len(V) + 122 - c)

"""Check alpha = delta^2 and phi (Frobenius) are collineations of H(9); report orders and cycle types."""
import numpy as np, math, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r5/c2')
import ncl
t0 = time.time()
lines, coord, code = ncl.load_hex(); N = len(coord)
alpha = ncl.alpha_perm(N)
phi = ncl.frob_perm(coord, code)
print('N', N, 'lines', len(lines), 'load s', round(time.time() - t0, 1))
print('alpha bijective & collineation:', ncl.is_collineation(alpha, lines))
print('phi   bijective & collineation:', ncl.is_collineation(phi, lines))
from collections import Counter
def lcm_of(lst):
    r = 1
    for x in lst: r = r * x // math.gcd(r, x)
    return r
cl = ncl.cycle_lengths(alpha); print('alpha order', lcm_of(cl), 'cycle type', sorted(Counter(cl).items()))
cp = ncl.cycle_lengths(phi); print('phi order', lcm_of(cp), 'cycle type', sorted(Counter(cp).items()))
# does alpha commute with phi?  (group <alpha, phi> is then abelian-ish; just report)
print('alpha phi == phi alpha:', bool((alpha[phi] == phi[alpha]).all()))
# is the duality itself an involution on lines/points?  alpha^m = id?  check alpha^k fixed-point counts
np.save('alpha.npy', alpha); np.save('phi.npy', phi)

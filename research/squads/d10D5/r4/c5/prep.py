import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
from lns import PM, LOF, N, PTS
S = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S['F']; sig0 = S['sig']
rows = S['rows']
F9 = [x for x in F if x != 65]
def swaps(sig, pairs):
    s = sig.copy(); sinv = np.empty(N, np.int64); sinv[s] = np.arange(N)
    for p, l in pairs:
        o = sinv[l]; t = s[p]; s[p] = l; s[o] = t; sinv[l] = p; sinv[t] = o
    return s
def write_base(fn, free, sig):
    with open(fn, 'w') as f:
        f.write(rows['dmhub'] and 'dmhub ' + ' '.join(rows['dmhub']) + '\n')
        f.write('free ' + ' '.join(map(str, free)) + '\n')
        f.write('sigma ' + ' '.join(str(int(x)) for x in sig) + '\n')
        for key in ('mv0', 'mv1', 'nu'):
            f.write(key + ' ' + ' '.join(rows[key]) + '\n')
if __name__ == '__main__':
    # usage: prep.py OUTBASE "p:l p:l ..."
    out = sys.argv[1]; pairs = [tuple(int(v) for v in t.split(':')) for t in sys.argv[2].split()] if len(sys.argv) > 2 else []
    free = F9 + [p for p, _ in pairs]
    sig = swaps(sig0, pairs)
    if pairs:
        for x in free:
            print('collinear count', x, int(sum(PM[x, y] for y in free if y != x)))
    write_base(out + '.sol', F9, sig0)   # base sigma is the 9-set's sigma before the forced swaps
    print('FREE=' + ' '.join(map(str, free)))
    print('cover (exact, new flags without hub edges)', lns.cover(free, sig, np.zeros((len(free), len(free)), bool)) if pairs else '')

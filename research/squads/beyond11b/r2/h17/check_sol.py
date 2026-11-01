import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers, nb_counts
p, k, r = 761, 19, 25
G = Frob(p, k, r)
lines = open('/home/user/degree-diameter/research/squads/beyond11b/r1/g02/sol_m761_k19_r25_s2.sol').read().split('\n')
S = [int(l.split()[0]) for l in lines[1:] if l.strip()]
print('S indices', S, 'labels j', [s % k for s in S], 'a', [s // k for s in S])
t = time.time()
XA, XB = covers(G, S, 11)
print('D=11 exact: |X_A| =', XA.sum(), 'holes A =', (~XA).sum(), '| |X_B| =', XB.sum(), 'holes B =', (~XB).sum(), 'time', round(time.time()-t,2))
# the same S must not be "e-free": check e in S
print('e in S:', 0 in S)
c = nb_counts(G, S, 10)
print('NB walks total (A side):', c.sum(), 'expected Delta(Delta-1)^(2h-1) =', len(S)*(len(S)-1)**9)
print('mean per element', c.mean(), 'zero-count elements', int((c==0).sum()))

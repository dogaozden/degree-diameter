import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
from hc import cost_fn
m, k, r = map(int, sys.argv[1:4]); S = [int(x) for x in sys.argv[4].split(',')]
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
S = np.array(S)
TA = prodset(T, Sinv[S], S); TB = prodset(T, S, Sinv[S])
PA = np.array([0]); PB = np.array([0])
for _ in range(4):
    PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
MA = np.setdiff1d(np.arange(N), PA); MB = np.setdiff1d(np.arange(N), PB)
show = lambda x: (int(x % m), int(x // m))
print("N", N, "|TA|", len(TA), "|TB|", len(TB), "cost", cost_fn(T, Sinv, S))
print("MA", [show(x) for x in MA], "inv", [show(Sinv[x]) for x in MA])
print("MB", [show(x) for x in MB], "inv", [show(Sinv[x]) for x in MB])
print("S", [show(x) for x in S])
# abelianisation: G/G' with G' = (r-1)Z_m; image (a mod gcd(r-1,m), j)
from math import gcd
print("gcd(r-1,m)", gcd(r-1, m))

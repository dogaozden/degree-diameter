import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c5')
from chartlib import *
q = 5
hint_pts = eval(open('hint5_chart.txt').read())
Qp = lambda t: (t[2] * t[2] - t[0] * t[3] - t[1] * t[4]) % q
a0 = hint_pts[0]
T = [tuple((x - y) % q for x, y in zip(t, a0)) for t in hint_pts]
cand = [t for t in T if t != (0,)*5 and Qp(t) in {1,4}]
v = cand[0]; lam = next(l for l in range(1,q) if (l*l*Qp(v))%q == 1)
S = [tuple((lam*x)%q for x in t) for t in T]
w1 = tuple((lam*x)%q for x in v)
idx = np.arange(q**5); V = np.stack([(idx//q**i)%q for i in range(5)],axis=1)
Bm = np.zeros((5,5),dtype=np.int64); Bm[2,2]=2; Bm[0,3]=Bm[3,0]=-1; Bm[1,4]=Bm[4,1]=-1
Qv = (V[:,2]**2 - V[:,0]*V[:,3] - V[:,1]*V[:,4]) % q
sing = np.nonzero(Qv==0)[0]; sing = sing[sing!=0]; Vs = V[sing]
first = np.argmax(Vs!=0,axis=1); P = Vs[Vs[np.arange(len(Vs)),first]==1]
print('singular proj points', len(P))
# check total singularity of planes and count conflicts within hint cosets
GM = (P @ Bm @ P.T) % q
i, j = 0, int(np.nonzero(GM[0,1:]==0)[0][0]) + 1
d1, d2 = P[i], P[j]
print('d1', d1, 'Q', (d1[2]**2-d1[0]*d1[3]-d1[1]*d1[4])%q, 'd2', d2, 'Q', (d2[2]**2-d2[0]*d2[3]-d2[1]*d2[4])%q, 'B', (d1@Bm@d2)%q)
Ns = nullspace_mod(np.stack([(d1@Bm)%q,(d2@Bm)%q]), q)
print('Ns', Ns)
for n in Ns:
    print(' check orth', ((d1@Bm@n)%q, (d2@Bm@n)%q))
# hint points in same coset of plane W? compute invariant for hint
Nm = np.array(Ns).T
inv_fn = lambda t: tuple(((np.array(t)@Bm@Nm)%q).tolist())
from collections import Counter
cnt = Counter(inv_fn(t) for t in S if t != w1 and t != (0,)*5)
print('max hint members in one coset of this plane:', max(cnt.values()))
# Also: does the plane span d1,d2 contain a difference of two hint points?
W = {tuple(((al*d1+be*d2)%q).tolist()) for al in range(q) for be in range(q)}
print('plane size', len(W), 'all singular', all((w[2]**2-w[0]*w[3]-w[1]*w[4])%q==0 for w in W))

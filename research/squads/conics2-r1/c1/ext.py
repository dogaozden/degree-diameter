import numpy as np, sys, collections, time
rel = np.load('/home/user/degree-diameter/research/squads/conics2-r1/c1/rel_q5.npz')
Pc, Pd4, Popp, Lc, Ld4, Lopp = [rel[k] for k in ['Pc','Pd4','Popp','Lc','Ld4','Lopp']]
N = Pc.shape[0]
lines = open('/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol').read().split('\n')
R = np.array([int(t) for t in lines[1].split()[1:]])
sig = np.array([int(t) for s in lines[3:] for t in s.split()], dtype=np.int64)
assert len(sig) == N and len(set(sig.tolist())) == N
F = sig[R]                       # f on R (lines)
print('R', len(R), 'F distinct', len(set(F.tolist())))
# check record consistency: R-R relations vs F-F relations
RR = Pd4[np.ix_(R, R)]; FF = Ld4[np.ix_(F, F)]
print('S2 check (d4 equal):', (RR == FF).all(), 'mismatch', (RR != FF).sum())
print('R-R collinear', Pc[np.ix_(R,R)].sum(), 'F-F concurrent', Lc[np.ix_(F,F)].sum())
# candidates for an extra point x and an extra line L
notR = np.ones(N, bool); notR[R] = False
Cx = np.nonzero(notR & ~Pc[:, R].any(1))[0]
CL = np.nonzero(~np.isin(np.arange(N), F) & ~Lc[:, F].any(1))[0]
print('candidate points', len(Cx), 'candidate lines', len(CL))
M1 = Pd4[np.ix_(Cx, R)].astype(np.uint8)          # d4 pattern of x vs R
M2 = Ld4[np.ix_(CL, F)].astype(np.uint8)          # d4 pattern of L vs F
# require x opposite-or-d4 to all R (no collinear already), and L similarly (no concurrency already)
keys = collections.defaultdict(list)
for i, row in enumerate(M2):
    keys[row.tobytes()].append(CL[i])
matches = []
for i, row in enumerate(M1):
    for L in keys.get(row.tobytes(), []):
        matches.append((int(Cx[i]), int(L)))
print('exact type matches (x, L):', len(matches))
if matches:
    x, L = matches[0]
    print('first match', x, L)
np.save('/home/user/degree-diameter/research/squads/conics2-r1/c1/ext_matches.npy', np.array(matches) if matches else np.zeros((0,2),int))

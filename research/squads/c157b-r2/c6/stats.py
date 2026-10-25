import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r2/shared')
import gperm
N = gperm.N; LP = gperm.LP; PL = gperm.PL
ld = lambda f: np.loadtxt(f, dtype=np.int64).reshape(-1)
P0, P1, S3, S4 = (ld(f) for f in ('P0.txt', 'P1.txt', 'S3.txt', 'S4.txt'))
Rp = ld('/home/user/degree-diameter/research/squads/c157b-r1/shared/Rp.txt') if False else None
print('P0 P1 overlap', len(np.intersect1d(P0, P1)), 'S3 S4 overlap', len(np.intersect1d(S3, S4)))
def cov_pts(lines):
    s = np.zeros(N, bool); s[lines] = True; return s
def cov_lines(pts):
    s = np.zeros(N, bool); s[pts] = True; return s[LP].any(1)
cS = np.zeros(N, np.int64); np.add.at(cS, LP[S3].reshape(-1), 1); np.add.at(cS, LP[S4].reshape(-1), 1)
print('points covered by S3 u S4 (incidence count distribution):', np.bincount(cS)[:4], 'nonzero', (cS > 0).sum())
for name, s in (('P0', P0), ('P1', P1)):
    print(name, 'paired elements', (lambda: 0)())
pc = np.zeros(N, np.int64); np.add.at(pc, PL[P0].reshape(-1), 1)
print('P0 lines met multiplicity', np.bincount(pc)[:4])
pcl = np.zeros(N, np.int64); np.add.at(pcl, PL[P1].reshape(-1), 1)
print('P1 lines met multiplicity', np.bincount(pcl)[:4])
lines_met = cov_lines(np.concatenate([P0, P1]))
print('lines meeting P0 u P1:', lines_met.sum())

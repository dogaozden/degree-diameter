# prep_starts.py: builds the point starting sets for dpack in c5/.
#  start_B.txt : Pfree_unmasked.txt filtered to allow_P2 (for each pair with an unallowed end, drop that end)
#  start_A.txt : copy of research/squads/c157b-r1/c4/best_P.txt (8,645 plain points)
#  start_C*.txt: images of RH.txt under random SL(3,11) collineations (gperm.perm_from_mat7)
import sys, numpy as np
SH = '/home/user/degree-diameter/research/squads/c157b-r2/shared'
sys.path.insert(0, SH)
import gperm
N = gperm.N; LP = gperm.LP
ld = lambda f: np.loadtxt(f, dtype=np.int64).reshape(-1)

def pairs_of(S):
    """returns (paired elements, partner array) for a point set S (ids), partner = -1 if none"""
    s = np.zeros(N, bool); s[S] = True
    partner = -np.ones(N, np.int64)
    nb = np.zeros(N, np.int64)
    for l in range(gperm.LP.shape[0]):
        pts = LP[l][s[LP[l]]]
        if len(pts) >= 2:
            for p in pts: nb[p] += len(pts) - 1
            if len(pts) == 2:
                partner[pts[0]] = pts[1]; partner[pts[1]] = pts[0]
    return nb, partner

allow = np.zeros(N, bool); allow[ld(f'{SH}/allow_P2.txt')] = True

# start_B: Pfree filtered to the mask
Pf = ld(f'{SH}/Pfree_unmasked.txt')
nb, partner = pairs_of(Pf)
drop = set()
done = set()
for e in Pf:
    f = partner[e]
    if f < 0 or e in done: continue
    done.add(e); done.add(f)
    if not allow[e] or not allow[f]:
        drop.add(e if not allow[e] else f)
keep = np.array([e for e in Pf if e not in drop], dtype=np.int64)
np.savetxt('start_B.txt', keep, fmt='%d')
nb2, _ = pairs_of(keep)
bad = sum(1 for e in keep if nb2[e] == 1 and not allow[e])
print(f'start_B: Pfree {len(Pf)} pairs {len(done)//2} dropped {len(drop)} -> {len(keep)}; paired {int((nb2==1).sum())} unallowed paired {bad}')

# start_A: the alternative 8,645-point set
A = ld('/home/user/degree-diameter/research/squads/c157b-r1/c4/best_P.txt')
nbA, _ = pairs_of(A)
np.savetxt('start_A.txt', A, fmt='%d')
print(f'start_A: {len(A)} points, paired {int((nbA>0).sum())}')

# start_C: images of RH under random SL(3,11) collineations
RH = ld(f'{SH}/RH.txt')
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
g = None
while True:
    g = rng.integers(0, 11, size=(3, 3))
    if int(round(np.linalg.det(g))) % 11 == 1: break
pp, lp = gperm.perm_from_mat7(gperm.sl3_to_mat7(g.reshape(-1).tolist()))
img = pp[RH]
nbC, _ = pairs_of(img)
np.savetxt('start_C.txt', img, fmt='%d')
print(f'start_C: g={g.reshape(-1).tolist()} image of RH: {len(img)} points, paired {int((nbC>0).sum())}')

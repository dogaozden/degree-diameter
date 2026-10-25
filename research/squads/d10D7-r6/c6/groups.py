# Build 3x3 generator matrices (GF(9), SL(3,9)) for the subgroups of the card, verify group orders,
# and save them to groups.pkl. Groups: SL33 (5616), SU33 (6048), A6 = Omega(3,9) (360), L27 (168), S91 = 91:3 (273).
import pickle, itertools, random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c6')
from h9 import *

def sig(A): return [[FROB[x] for x in r] for r in A]
def E(i, j, t=1):
    M = ident(); M[i][j] = t; return M
out = {}

# ---- SL(3,3) ----
sl33 = [E(0, 1), E(1, 0), E(1, 2), E(2, 1)]
print('SL33 order', closure(sl33, cap=10000), flush=True)
out['SL33'] = sl33

# ---- SU(3,3): unitary w.r.t. antidiagonal Hermitian form, condition g^T J sigma(g) = J ----
J = [[0, 0, 1], [0, 1, 0], [1, 0, 0]]
def is_unitary(g): return mm(mm(tr(g), J), sig(g)) == J
up = []; lo = []
for x, y, z in itertools.product(range(9), repeat=3):
    u = [[1, x, y], [0, 1, z], [0, 0, 1]]
    if is_unitary(u) and (x, y, z) != (0, 0, 0): up.append(u)
    l = [[1, 0, 0], [x, 1, 0], [y, z, 1]]
    if is_unitary(l) and (x, y, z) != (0, 0, 0): lo.append(l)
tor = []
for a in range(1, 9):
    g = [[a, 0, 0], [0, MULL[a][a], 0], [0, 0, MULL[MULL[INV[a]][INV[a]]][INV[a]]]]
    if is_unitary(g) and det3(g) == 1: tor.append(g)
print('unitary root elements up/lo', len(up), len(lo), 'torus', len(tor), flush=True)
su_gens = up[:6] + lo[:6] + tor[:1]
o = closure(su_gens, cap=7000)
print('SU33 order from generators', o, flush=True)
if o != 6048:
    su_gens = up + lo + tor
    print('SU33 order with all gens', closure(su_gens, cap=7000), flush=True)
out['SU33'] = su_gens

# ---- Omega(3,9) = A6 as adjoint image of SL(2,9) on trace-zero matrices ----
def mm2(A, B):
    return [[ADDL[MULL[A[i][0]][B[0][j]]][MULL[A[i][1]][B[1][j]]] for j in range(2)] for i in range(2)]
def ad(g):
    p, qq, r, s = g[0][0], g[0][1], g[1][0], g[1][1]
    gi = [[s, NEG[qq]], [NEG[r], p]]
    cols = []
    for X in ([[1, 0], [0, NEG[1]]], [[0, 1], [0, 0]], [[0, 0], [1, 0]]):
        Y = mm2(mm2(g, X), gi)
        assert ADDL[Y[0][0]][Y[1][1]] == 0
        cols.append([Y[0][0], Y[0][1], Y[1][0]])
    return [[cols[j][i] for j in range(3)] for i in range(3)]
sl2 = [[[1, 1], [0, 1]], [[1, 3], [0, 1]], [[1, 0], [1, 1]], [[1, 0], [3, 1]]]
a6_gens = [ad(g) for g in sl2]
print('A6 order', closure(a6_gens, cap=2000), 'dets', [det3(g) for g in a6_gens], flush=True)
out['A6'] = a6_gens

# ---- Singer torus of order 91 and normaliser 91:3 ----
d = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r6/c6/grp.pkl', 'rb'))
g91 = d['g']
def companion(a, b, c): return [[0, 0, NEG[c]], [1, 0, NEG[b]], [0, 1, NEG[a]]]
def has_root(a, b, c):
    for t in range(9):
        t2 = MULL[t][t]; t3 = MULL[t2][t]
        s = ADDL[ADDL[t3][MULL[a][t2]]][ADDL[MULL[b][t]][c]]
        if s == 0: return True
    return False
random.seed(1)
Mc = None
for trial in range(2000):
    a, b, c = random.randrange(9), random.randrange(9), random.randrange(1, 9)
    if has_root(a, b, c): continue
    M0 = companion(a, b, c); g2 = mpow(M0, 8)
    if g2 == g91: Mc = M0; break
assert Mc is not None
M9 = mpow(Mc, 9); M18 = mpow(Mc, 18)
Phi = [[1 if i == 0 and j == 0 else 0 for j in range(3)] for i in range(3)]
Phi = [[0, 0, 0] for _ in range(3)]
for j, Mk in enumerate([ident(), M9, M18]):
    for i in range(3): Phi[i][j] = Mk[i][0]
dPhi = det3(Phi)
lam = FROB[INV[dPhi]]
Phip = [[MULL[lam][x] for x in r] for r in Phi]
assert det3(Phip) == 1
assert mm(mm(Phip, g91), inv3(Phip)) == mpow(g91, 9)
print('Phi det', dPhi, 'lam', lam, 'Phi normalises <g> with g -> g^9: OK', flush=True)
s91 = [g91, Phip]
print('91:3 order', closure(s91, cap=2000), flush=True)
out['S91'] = s91
out['g91'] = g91

# ---- L2(7) = <A, T>, A = g^13 of order 7, T involution with (TA)^3 = 1 ----
A7 = mpow(g91, 13)
print('A7 order', closure([A7], cap=100), flush=True)
pg = [v for v in itertools.product(range(9), repeat=3) if any(v) and v[next(k for k in range(3) if v[k])] == 1]
print('PG(2,9) reps', len(pg), flush=True)
found = []
cnt3 = 0
for v in pg:
    for w in itertools.product(range(9), repeat=3):
        if ADDL[ADDL[MULL[v[0]][w[0]]][MULL[v[1]][w[1]]]][MULL[v[2]][w[2]]] != 1: continue
        T = [[ADDL[MULL[2][MULL[v[i]][w[j]]]][(2 if i == j else 0)] for j in range(3)] for i in range(3)]
        # involution check T^2 = I and det 1
        if mm(T, T) != ident(): continue
        Y = mm(T, A7)
        if mm(mm(Y, Y), Y) != ident(): continue
        cnt3 += 1
        o = closure([A7, T], cap=400)
        if o is not None and o == 168:
            found.append(T)
            break
    if found: break
print('involutions with (TA)^3=1 tried', cnt3, 'L2(7) found', len(found), flush=True)
if found:
    out['L27'] = [A7, found[0]]
    print('L27 order check', closure([A7, found[0]], cap=500), flush=True)
pickle.dump(out, open('/home/user/degree-diameter/research/squads/d10D7-r6/c6/groups.pkl', 'wb'))
print('saved groups.pkl with', sorted(out))

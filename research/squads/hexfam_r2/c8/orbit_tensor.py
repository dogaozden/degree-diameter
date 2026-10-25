"""c8 wildcard: orbit-union clique for groups built from the tensor decomposition
    GF(q)^7 = (GF(q)^3 (x) GF(q)^2) + GF(q)   (7-dim quadratic space, Gram = kron(G3,G2) + [a]).
Group = (subgroup of O(G3)) (x) 1  (+ optional reflection in the last coordinate), i.e. PGL2(q)=SO3(q) on Sym^2 (x) H.
Orbits of the group on the points of Q(6,q); a valid orbit is self-opposite; orbit pairs compatible iff all cross
pairs opposite (checked with one representative per orbit, valid by transitivity). Exact max-weight clique on orbits.
usage: python3 orbit_tensor.py Q KIND TLIMIT OUTFILE   (KIND in o3, so3, so3e, o3hyp, so3hyp, so3ell)
"""
import sys, random, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, orbits, inv_mod, A7
from mwc import max_weight_clique

q, kind, tlimit, outfile = int(sys.argv[1]), sys.argv[2], float(sys.argv[3]), sys.argv[4]
rng = random.Random(7)
G = Geo(q); N = G.N

def refl(Gram, v):
    v = np.array(v, dtype=np.int64) % q; Gm = np.array(Gram, dtype=np.int64) % q
    vg = (v @ Gm) % q; nn = int(vg @ v) % q
    assert nn != 0
    R = (np.eye(len(v), dtype=np.int64) - 2 * np.outer(v, vg) * pow(nn, q - 2, q)) % q
    assert (((R.T @ Gm @ R) - Gm) % q == 0).all()
    return R

def rand_aniso(Gram, k, nrefl):
    out = []
    while len(out) < nrefl:
        v = [rng.randrange(q) for _ in range(k)]
        if any(v) and int(np.array(v) @ np.array(Gram) @ np.array(v)) % q:
            out.append(v)
    return out

I3 = np.eye(3, dtype=np.int64)
G3 = I3                                   # sum of three squares on V3 (orthogonal group O3(q))
if kind in ('o3hyp', 'so3hyp'):           # V2 hyperbolic plane (O2^+ : dihedral 2(q-1))
    G2 = np.array([[0, 1], [1, 0]])
elif kind in ('so3ell',):                 # V2 anisotropic (O2^- : dihedral 2(q+1)); nonsquare nu
    nu = next(x for x in range(2, q) if pow(x, (q - 1) // 2, q) == q - 1)
    G2 = np.array([[1, 0], [0, (-nu) % q]])
else:
    G2 = np.array([[0, 1], [1, 0]])
Gram6 = np.kron(G3, G2) % q
Gram7 = np.zeros((7, 7), dtype=np.int64); Gram7[:6, :6] = Gram6; Gram7[6, 6] = 1
T = None
from q6lib import inv_mod as _inv
# Use to_std for our coordinates
G_std = Geo(q)
T = G_std.to_std(Gram7)
Ti = inv_mod(T, q)

def lift6(g3, g2):          # 6x6 (x) block, 7x7 with e fixed
    M = np.zeros((7, 7), dtype=np.int64); M[:6, :6] = np.kron(g3, g2) % q; M[6, 6] = 1
    return M

def lift_e(M6):
    M = np.zeros((7, 7), dtype=np.int64); M[:6, :6] = M6; M[6, 6] = 1; return M

gens_abs = []
if kind in ('o3', 'o3hyp', 'so3ell'):
    # projective O3 (x) O2 with the 7th coordinate: reflections in V3 tensored with I2
    for v in rand_aniso(G3, 3, 4):
        gens_abs.append(lift6(refl(G3, v), np.eye(2, dtype=np.int64)))
if kind in ('so3', 'so3hyp'):
    # rotations: products of pairs of reflections in V3 (det 1 part of O3)
    refs = [refl(G3, v) for v in rand_aniso(G3, 3, 4)]
    for a, b in [(0, 1), (1, 2), (2, 3), (0, 3)]:
        gens_abs.append(lift6((refs[a] @ refs[b]) % q, np.eye(2, dtype=np.int64)))
if kind == 'so3e':
    refs = [refl(G3, v) for v in rand_aniso(G3, 3, 4)]
    for a, b in [(0, 1), (1, 2), (2, 3), (0, 3)]:
        gens_abs.append(lift6((refs[a] @ refs[b]) % q, np.eye(2, dtype=np.int64)))
    gens_abs.append(np.diag([1] * 6 + [q - 1]).astype(np.int64))   # reflection in e
if kind == 'so3ell':   # PGL2 (x) SO2^-: add the rotation of the anisotropic plane
    refs2 = [refl(G2, v) for v in rand_aniso(G2, 2, 2)]
    gens_abs.append(lift6(np.eye(3, dtype=np.int64), (refs2[0] @ refs2[1]) % q))
if kind == 'o3hyp':
    refs2 = [refl(G2, v) for v in rand_aniso(G2, 2, 2)]
    gens_abs.append(lift6(np.eye(3, dtype=np.int64), refs2[0]))
if kind == 'so3hyp':
    refs2 = [refl(G2, v) for v in rand_aniso(G2, 2, 2)]
    gens_abs.append(lift6(np.eye(3, dtype=np.int64), (refs2[0] @ refs2[1]) % q))

# check isometry of the 7-dim Gram, then conjugate to our coordinates
gens = []
for g in gens_abs:
    assert (((g.T @ Gram7 @ g) - Gram7) % q == 0).all(), 'not an isometry'
    M = (T @ g @ Ti) % q
    chk = (M.T @ A7 @ M - A7) % q
    assert ((chk % q) == 0).all() or True
    gens.append(M)

t0 = time.time()
# similitude check (should be scalar multiple of A7)
for M in gens:
    X = (M.T @ A7 @ M) % q
    c = X[0, 4]
    assert ((X - c * A7) % q == 0).all() or ((X - c * A7) % q == 0).all(), 'not in O7'
perms = [G.perm(M) for M in gens]
lab = orbits(N, perms)
no = int(lab.max()) + 1
sizes = np.bincount(lab, minlength=no)
rep = np.zeros(no, dtype=np.int64) - 1
order = np.argsort(lab, kind='stable'); starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
rep = order[starts]
print('group gens', len(gens), 'orbits', no, 'time', round(time.time() - t0, 1), flush=True)
print('orbit sizes (top):', sorted(sizes.tolist(), reverse=True)[:20], flush=True)

valid = np.zeros(no, dtype=bool); zc_all = np.zeros((no, no), dtype=np.int64) if no <= 3000 else None
Cp = G.C
zeros_rep = {}
for L in range(no):
    p = rep[L]
    z = (G.B(Cp[p:p + 1], Cp)[0] == 0)
    zc = np.bincount(lab, weights=z.astype(np.float64), minlength=no).astype(np.int64)
    zeros_rep[L] = zc
    valid[L] = (zc[L] == 1)           # only the representative itself (B(p,p)=0)
vidx = np.nonzero(valid)[0]
print('valid orbits', len(vidx), 'sizes', sorted(sizes[vidx].tolist(), reverse=True)[:20], flush=True)
pos = {int(L): k for k, L in enumerate(vidx)}
w = [int(sizes[L]) for L in vidx]
adj = [0] * len(vidx)
for a, L in enumerate(vidx):
    zc = zeros_rep[int(L)]
    for b, M_ in enumerate(vidx):
        if b != a and zc[M_] == 0:
            adj[a] |= 1 << b
best, verts, exact = max_weight_clique(w, adj, tlimit)
pts = []
for k in verts:
    L = int(vidx[k]); pts += np.nonzero(lab == L)[0].tolist()
pts = sorted(int(x) for x in pts)
ok, ext = G.check_opp(pts) if pts else (True, 0)
print('RESULT q', q, 'kind', kind, 'score', len(pts), 'orbits', len(verts), 'exact', exact, 'opp_ok', ok, 'time', round(time.time() - t0, 1), flush=True)
with open(outfile, 'w') as f:
    f.write(' '.join(map(str, pts)) + '\n')

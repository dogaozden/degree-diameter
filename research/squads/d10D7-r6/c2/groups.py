# c2 (round 6): orbit unions of subgroups of Sp(6,8) that are not inside a conjugate of Sp(6,2).
# usage: python3 groups.py NAME [NAME ...]   (NAME = key of GROUPS below, or "all")
# For each group: orbits on the 37449 points of H(8) (= PG(5,8)), self-compatible orbits, exact (time-limited)
# max-weight clique of the orbit compatibility graph, union written to c2/best_NAME.txt and scored with setcheck.
import numpy as np, sys, time, subprocess, json, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c4')
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid')
from common import V, Bval, MT, INVA, N, perm_from_matrix, perm_frobenius, inv_transpose, write_ids
from subgeo import orbits, orbit_graph, max_weight_clique

HERE = os.path.dirname(os.path.abspath(__file__))
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
SETCHECK = '/home/user/degree-diameter/research/squads/d10D7-r4/tools/setcheck'
PAIRS = [(0, 3), (1, 4), (2, 5)]          # hyperbolic pairs of B (coordinates of V)
TL = float(os.environ.get('CLIQUE_TL', '60'))

def mm(A, B):
    A = np.asarray(A, dtype=np.int64); B = np.asarray(B, dtype=np.int64)
    n, k = A.shape; m = B.shape[1]; C = np.zeros((n, m), dtype=np.int64)
    for i in range(n):
        for j in range(m):
            s = 0
            for t in range(k): s ^= int(MT[A[i, t], B[t, j]])
            C[i, j] = s
    return C
def mpow(A, e):
    A = np.asarray(A, dtype=np.int64); R = np.eye(A.shape[0], dtype=np.int64)
    for _ in range(e): R = mm(R, A)
    return R
def mat_order(A, limit=600):
    A = np.asarray(A, dtype=np.int64); I = np.eye(A.shape[0], dtype=np.int64); P = A.copy()
    for k in range(1, limit):
        if np.array_equal(P, I): return k
        P = mm(P, A)
    return None
def frobm(A): A = np.asarray(A, dtype=np.int64); return MT[A, A]      # entrywise x -> x^2
def emb2(blocks):
    """2x2 GF(8) blocks on the three hyperbolic pairs (0,3), (1,4), (2,5) of the symplectic space."""
    G = np.zeros((6, 6), dtype=np.int64)
    for (i, j), M in zip(PAIRS, blocks):
        M = np.asarray(M, dtype=np.int64)
        G[i, i], G[i, j], G[j, i], G[j, j] = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return G
def coord_perm(pi):
    G = np.zeros((6, 6), dtype=np.int64)
    for c in range(6): G[pi[c], c] = 1
    return G
SIGMA = coord_perm({0: 1, 1: 2, 2: 0, 3: 4, 4: 5, 5: 3})     # cyclic permutation of the three pairs
TAU = coord_perm({0: 1, 1: 0, 2: 2, 3: 4, 4: 3, 5: 5})       # transposition of pairs 0 and 1
def levi(A):
    """diag(A, A^-T) in GL(3,8) x GL(3,8) acting on (x0,x1,x2 | x3,x4,x5): symplectic since B = x.w_y + y.w_x."""
    A = np.asarray(A, dtype=np.int64); G = np.zeros((6, 6), dtype=np.int64)
    G[:3, :3] = A; G[3:, 3:] = np.asarray(inv_transpose(A.tolist()), dtype=np.int64)
    return G
def gf_nullspace(K):
    K = [[int(x) for x in r] for r in K]; m = len(K); n = len(K[0]); piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if K[i][c]), None)
        if p is None: continue
        K[r], K[p] = K[p], K[r]; iv = int(INVA[K[r][c]]); K[r] = [int(MT[iv, x]) for x in K[r]]
        for i in range(m):
            if i != r and K[i][c]:
                f = K[i][c]; K[i] = [x ^ int(MT[f, y]) for x, y in zip(K[i], K[r])]
        piv.append(c); r += 1
        if r == m: break
    basis = []
    for fc in [c for c in range(n) if c not in piv]:
        x = [0] * n; x[fc] = 1
        for i, pc in enumerate(piv): x[pc] = K[i][fc]
        basis.append(x)
    return basis

# ---- building blocks -------------------------------------------------------------------------------
I2 = np.eye(2, dtype=np.int64)
X = lambda t: np.array([[1, t], [0, 1]], dtype=np.int64)     # elementary matrices of SL(2,8)
Y = lambda t: np.array([[1, 0], [t, 1]], dtype=np.int64)
S8GENS = [M for t in (1, 2, 4) for M in (X(t), Y(t))]         # t in a GF(2)-basis of GF(8): generate SL(2,8)
ALPHA = 2                                                    # primitive element x of GF(8)
TORUS7 = np.array([[ALPHA, 0], [0, int(INVA[ALPHA])]], dtype=np.int64)     # split torus, order 7
M9 = next(np.array([[0, 1], [1, c]], dtype=np.int64) for c in range(8)
          if mat_order(np.array([[0, 1], [1, c]])) == 9)          # non-split torus element, order 9
P2 = np.array([[0, 1], [1, 0]], dtype=np.int64)                # with M9 generates D18 (inverts M9)

def singer():
    for a in range(8):
        for b in range(8):
            for c in range(1, 8):
                C = np.array([[0, 0, c], [1, 0, b], [0, 1, a]], dtype=np.int64)
                if mat_order(C, limit=512) == 511: return C
    raise SystemExit('no primitive cubic')
C511 = singer()
C73 = mpow(C511, 7)                                            # order 73
def normaliser_elt():
    """F with F C F^-1 = C^8 (Frobenius of GF(512)/GF(8)) and F^3 = I; all solutions are F0*g."""
    D = mpow(C511, 8); K = []
    for i in range(3):
        for j in range(3):
            row = [0] * 9
            for k in range(3): row[3 * i + k] ^= int(C511[k, j])
            for k in range(3): row[3 * k + j] ^= int(D[i, k])
            K.append(row)
    basis = gf_nullspace(K); import itertools
    for coef in itertools.product(range(8), repeat=len(basis)):
        if not any(coef): continue
        vec = [0] * 9
        for c, b in zip(coef, basis):
            for t in range(9): vec[t] ^= int(MT[c, b[t]])
        F = np.array(vec, dtype=np.int64).reshape(3, 3)
        if np.array_equal(mpow(F, 3), np.eye(3, dtype=np.int64)) and mat_order(F, 6) == 3: return F
    raise SystemExit('no order-3 normaliser')
FSING = normaliser_elt()

def blk_on(k, M):   # M (2x2) on pair k, identity elsewhere
    bl = [I2, I2, I2]; bl[k] = M; return emb2(bl)

def groups_def():
    FROB = perm_frobenius()
    Delta = [emb2([M, M, M]) for M in S8GENS]
    Delta_tw = [emb2([M, frobm(M), frobm(frobm(M))]) for M in S8GENS]
    S8_wr_S3 = [blk_on(k, M) for k in range(3) for M in S8GENS] + [SIGMA, TAU]
    C9_3 = [blk_on(k, M9) for k in range(3)]
    D18_3 = [blk_on(k, M9) for k in range(3)] + [blk_on(k, P2) for k in range(3)]
    C7_3 = [blk_on(k, TORUS7) for k in range(3)]
    return {
        'D1_Delta_SL28': Delta,
        'D2_DeltaTwisted': Delta_tw,
        'D3_Delta_x_C3pairs': Delta + [SIGMA],
        'D4_Delta_x_Frob': Delta + [FROB],
        'D5_DeltaTw_x_C3pairs': Delta_tw + [SIGMA],
        'D6_DeltaTw_x_Frob': Delta_tw + [FROB],
        'D7_SL28wrS3': S8_wr_S3,
        'D8_C9cubed': C9_3,
        'D9_C9cubed_x_C3': C9_3 + [SIGMA],
        'D10_D18cubed_x_S3': D18_3 + [SIGMA, TAU],
        'D11_C7cubed_x_S3': C7_3 + [SIGMA, TAU],
        'L1_Singer511': [levi(C511)],
        'L2_Singer73': [levi(C73)],
        'L3_Singer73_3': [levi(C73), levi(FSING)],
        'L4_Singer511_3': [levi(C511), levi(FSING)],
    }

def check_aut(p, n=4000, seed=0):
    rng = np.random.default_rng(seed); a = rng.integers(0, N, n); b = rng.integers(0, N, n)
    return bool(np.array_equal(Bval(V[a], V[b]) != 0, Bval(V[p[a]], V[p[b]]) != 0))


def orbit_graph2(lab, maxsize=457):
    """same as subgeo.orbit_graph, but orbits larger than maxsize (a partial ovoid of W(5,8) has <= 457 points)
    are never self-compatible, so they are skipped instead of building an |O| x |O| matrix."""
    no = lab.max() + 1; order_ = np.argsort(lab, kind='stable')
    cuts = np.cumsum(np.bincount(lab, minlength=no)); members = np.split(order_, cuts[:-1])
    sizes = np.array([len(m) for m in members]); sc = np.zeros(no, bool)
    for o, m in enumerate(members):
        if len(m) > maxsize: continue
        X = V[m]; Bm = Bval(X[:, None, :], X[None, :, :]) != 0; np.fill_diagonal(Bm, True); sc[o] = Bm.all()
    S = np.nonzero(sc)[0]
    if len(S) == 0: return sizes, members, S, np.zeros((0, 0), bool)
    order = np.concatenate([members[o] for o in S]); starts = np.concatenate([[0], np.cumsum(sizes[S])[:-1]])
    A = np.zeros((len(S), len(S)), bool)
    for a, o in enumerate(S):
        r = members[o][0]; ok = Bval(V[r][None, :], V) != 0
        A[a] = np.logical_and.reduceat(ok[order], starts)
    A = A & A.T; np.fill_diagonal(A, False)
    return sizes, members, S, A

def run(name, gens):
    t0 = time.time()
    perms = [g if isinstance(g, np.ndarray) and g.shape == (N,) else perm_from_matrix(g) for g in gens]
    assert all(check_aut(p) for p in perms), 'generator does not preserve opposition'
    lab = orbits(perms); t1 = time.time()
    sizes, members, S, A = orbit_graph2(lab); t2 = time.time()
    nS = len(S)
    rec = {'group': name, 'orbits': int(len(sizes)), 'selfcompat': int(nS), 'gens': len(gens)}
    if nS == 0:
        rec.update(best=0, exact=True)
    else:
        w = sizes[S].tolist()
        bw, cl, exact = max_weight_clique(A, w, time_limit=TL); t3 = time.time()
        orbs = [int(S[c]) for c in cl]
        ids = np.sort(np.concatenate([members[o] for o in orbs])) if orbs else np.array([], dtype=np.int64)
        path = os.path.join(HERE, 'best_%s.txt' % name)
        write_ids(path, ids)
        out = subprocess.run([SETCHECK, HEX, path, 'points', 'opposite'], capture_output=True, text=True).stdout.strip()
        rec.update(best=int(len(ids)), exact=bool(exact), orbit_sizes=sorted(sizes[orbs].tolist(), reverse=True)[:40],
                   file=path, setcheck=out, clique_s=round(t3 - t2, 1))
    rec['time_s'] = round(time.time() - t0, 1)
    print(json.dumps(rec), flush=True)
    with open(os.path.join(HERE, 'results.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
    return rec

if __name__ == '__main__':
    G = groups_def()
    names = list(G) if sys.argv[1:] in ([], ['all']) else sys.argv[1:]
    for nm in names:
        key = [k for k in G if k == nm or k.startswith(nm + '_')] if nm not in G else [nm]
        if not key: print('unknown group', nm, flush=True); continue
        run(key[0], G[key[0]])

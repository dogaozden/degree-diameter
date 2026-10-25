# c4: orbit pipeline. usage: python3 run_orb.py NAME   (NAME: T<k> = order-k subgroup of the norm-1 torus (translations
# by 73 in the L-model), L73 = order-73 Levi torus diag(A, A^-T) of Sp(6,8), TF<k> = <T_k, Frobenius> style groups)
import numpy as np, sys, time
sys.path.insert(0, '.')
from common import *
name = sys.argv[1]
M = np.load('L2H.npy')
def trans(t):
    p = np.zeros(N, dtype=np.int64); p[M] = M[(np.arange(N) + t) % N]; return p
def singer_levi():
    best = None
    for a in range(8):
        for b in range(8):
            for c in range(1, 8):
                C = [[0, 0, c], [1, 0, b], [0, 1, a]]
                P = [[int(i == j) for j in range(3)] for i in range(3)]
                ordc = None
                for k in range(1, 512):
                    P = mat_mul(P, C).tolist()
                    if P == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]: ordc = k; break
                if ordc == 511:
                    return C
    raise SystemExit('no primitive cubic found')
def blockdiag(A, B):
    G = [[0] * 6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            G[i][j] = A[i][j]; G[i + 3][j + 3] = B[i][j]
    return G
t0 = time.time()
if name.startswith('T'):
    k = int(name[1:]); gens = [trans(37449 // k)]
elif name == 'L73':
    C = singer_levi()
    Cp = [[0] * 3 for _ in range(3)]
    A = [[int(i == j) for j in range(3)] for i in range(3)]
    for _ in range(7): A = mat_mul(A, C).tolist()   # A = C^7 has order 73
    gens = [perm_from_matrix(blockdiag(A, inv_transpose(A)))]
    print('Singer companion', C, 'A = C^7', A, flush=True)
else:
    raise SystemExit('unknown group ' + name)
orb, members = orbits_from_perms(gens)
sizes = np.array([len(m) for m in members])
print(name, 'orbits', len(members), 'size histogram', dict(zip(*np.unique(sizes, return_counts=True))), flush=True)
sc = selfcompat(members)
S = np.nonzero(sc & (sizes == sizes.max()))[0]
print('self-compatible orbits of max size', len(S), 'time %.1f' % (time.time() - t0), flush=True)
A = compat_matrix(S, members)
print('compat density', A.sum() / max(1, len(S) * (len(S) - 1)), 'time %.1f' % (time.time() - t0), flush=True)
np.save(name + '_S.npy', S)
write_mis_graph(name + '_conf.bin', S, members, A)
print('wrote', name + '_conf.bin', flush=True)

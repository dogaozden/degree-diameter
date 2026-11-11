# fam2.py (worker c7b): small formula-family tests at q (prime or any q with hex file), m; cost via hexeval ITERS=0.
# families:
#   R    : random matchings, random voltages (baseline, same as hexeval HZERO=0 up to RNG)
#   IL   : index-linear: sig_1(i) = i + s (mod N), sig_2 = random; mv_1(i) = (c*i) mod m; hex random
#   T2   : hexagon voltages two-valued {0, c} (c random per sample); matchings random
#   BIL  : hexagon voltage = (B(x_p, z_l) mod q) * c mod m with x_p point coordinates and z_l = coordinates of the
#          point with the same index as the line (not incident in general); matchings random.
# usage: fam2.py Q M FAMILY NSAMP SEED0
import sys, os, random, math, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fam import read_hex, write_sol, evaluate, HERE
q, m, fam, ns, seed0 = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
N, lines = read_hex(q)
with open(os.path.join(HERE, 'hex', 'hex_q%d.bin' % q), 'rb') as f:
    f.read(12); f.read(4 * N * (q + 1)); coords = f.read(N * 7)
X = [[coords[7 * i + j] for j in range(7)] for i in range(N)]
Q1 = q + 1
def B(x, y):   # polar form of the quadric X0X4+X1X5+X2X6=X3^2 (odd q), mod q
    return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % q
res = []
tmp = os.path.join(HERE, 'runs', 'fam2_tmp_%s_q%d_m%d.sol' % (fam, q, m))
for s in range(ns):
    rng = random.Random(seed0 * 100003 + s)
    sig = []
    for t in range(2):
        perm = list(range(N)); rng.shuffle(perm); sig.append(perm)
    mv = [[rng.randrange(m) for _ in range(N)] for t in range(2)]
    hv = [rng.randrange(m) for _ in range(N * Q1)]
    if fam == 'IL':
        sh = rng.randrange(1, N); c = rng.randrange(1, m)
        sig[0] = [(i + sh) % N for i in range(N)]
        mv[0] = [(c * i) % m for i in range(N)]
    elif fam == 'T2':
        c = rng.randrange(1, m); hv = [c if rng.random() < 0.5 else 0 for _ in range(N * Q1)]
    elif fam == 'Z2':   # hexagon voltages in {0, m/2} (Z_2 gain graph), matchings uniform
        hv = [(m // 2) if rng.random() < 0.5 else 0 for _ in range(N * Q1)]
    elif fam == 'BIL':
        c = rng.randrange(1, m)
        hv = [0] * (N * Q1)
        for l in range(N):
            for k in range(Q1):
                p = lines[l][k]
                hv[l * Q1 + k] = (B(X[p], X[l]) * c) % m
    if fam == 'LAY':   # hexagon voltage = random table value eps[(dist(p0,p), dist(p0,l))] (layers from point 0)
        if s == 0:
            from collections import deque
            pl_of_p = [[] for _ in range(N)]
            for l in range(N):
                for k in range(Q1):
                    pl_of_p[lines[l][k]].append(l)
            LAYP = [None] * N; LAYL = [None] * N
            LAYP[0] = 0; dq = deque([('p', 0)])
            while dq:
                side, i = dq.popleft()
                if side == 'p':
                    for l in pl_of_p[i]:
                        if LAYL[l] is None:
                            LAYL[l] = LAYP[i] + 1; dq.append(('l', l))
                else:
                    for k in range(Q1):
                        p2 = lines[i][k]
                        if LAYP[p2] is None:
                            LAYP[p2] = LAYL[i] + 1; dq.append(('p', p2))
        eps = {}
        for a in range(8):
            for b in range(8):
                eps[(a, b)] = rng.randrange(m)
        hv = [eps[(LAYP[lines[l][k]], LAYL[l])] for l in range(N) for k in range(Q1)]
    write_sol(tmp, q, m, 2, sig, mv, hv)
    pc, dup = evaluate(q, m, tmp)
    res.append(pc + 100 * dup)
res.sort()
n = len(res)
print('q=%d m=%d family=%s samples=%d zero=%d mean=%.2f median=%d min=%d' %
      (q, m, fam, n, sum(1 for r in res if r == 0), sum(res) / n, res[n // 2], res[0]))

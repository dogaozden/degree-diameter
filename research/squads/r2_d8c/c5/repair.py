"""Targeted repair of the pencil design at q = 9 (own-d8-compound, r2 card c5).

Local search over the voltage pair (f1, f2) of single points u (the two parallel duality edges u -- delta(u)),
objective = glift COST on the fixed sources r:64:1. Candidate points for the failing pairs (x, t) taken from a
glift dump of the initial design: a duality edge u--delta(u) can serve a walk of length <= 7 from x to t iff
d(x,u) + d(delta(u),t) <= 6 or d(x,delta(u)) + d(u,t) <= 6 (H-distances). Axis points (no pencil value) are
candidates too.

usage: repair.py m seed budget_seconds dumpfile out_prefix [max_pairs]
"""
import sys, time, subprocess, re, random, numpy as np
HEX = '/home/user/degree-diameter/research/squads/cells/d10D8_work'
sys.path.insert(0, HEX)
from hexlib import load
PD = open(HEX + '/pencil_dual.py').read()
exec(PD[PD.index('def gf_tables'):PD.index('q, phif, m, seed, out')])   # gf_tables exactly as in pencil_dual.py

m, seed, budget, dumpf, outp = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4], sys.argv[5]
max_pairs = int(sys.argv[6]) if len(sys.argv) > 6 else 40
q = 9
N, LP, PL, coord = load(q)
phi = np.fromfile('/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi', dtype=np.int32).astype(np.int64)
C = coord.astype(np.int64)
rng = np.random.default_rng(seed)
ADD, MUL, NEG, INV = gf_tables(q)
a = rng.integers(0, q, 7); a2 = rng.integers(0, q, 7)
PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
two = ADD[1][1]
def bform(x, y):
    acc = 0
    for i, j in PAIRS:
        acc = ADD[acc][MUL[x[i]][y[j]]]
    return ADD[acc][NEG[MUL[two][MUL[x[3]][y[3]]]]]
c = np.zeros(N, dtype=np.int64); axis = np.zeros(N, bool)
for p in range(N):
    s_, t_ = bform(C[p], a), bform(C[p], a2)
    if t_ != 0: c[p] = MUL[s_][INV[t_]]
    elif s_ != 0: c[p] = q
    else: axis[p] = True
spec = rng.integers(0, q + 1, N)
c = np.where(axis, spec, c)
F1 = ((1 + c) % m).astype(np.int64); F2 = ((q + 2 + c) % m).astype(np.int64)
axis_idx = np.nonzero(axis)[0]

# combined adjacency of H(q): 0..N-1 points, N..2N-1 lines
ADJ = np.zeros((2 * N, q + 1), dtype=np.int64)
ADJ[:N] = PL + N
ADJ[N:] = LP
def bfs(x):
    dist = np.full(2 * N, 99, dtype=np.int64); dist[x] = 0
    fr = np.array([x]); d = 0
    while fr.size and d < 6:
        d += 1
        nb = np.unique(ADJ[fr].ravel()); nb = nb[dist[nb] == 99]
        dist[nb] = d; fr = nb
    return dist

# header and hexagon darts (fixed part of every file)
HEAD = (f'Z {m}\n{2 * N}\n' + ' '.join(['0'] * N + ['1'] * N) + '\n'
        + ''.join(f'{p} {N + l} 0\n' for l in range(N) for p in LP[l]))
PRE = [f'{p} {phi[p]} ' for p in range(N)]
def write(G1, G2, path):
    v = ''.join(f'{PRE[p]}{G1[p]}\n{PRE[p]}{G2[p]}\n' for p in range(N))
    with open(path, 'w') as fh:
        fh.write(HEAD + v)

def glift(path, spec_):
    r = subprocess.run(['nice', '-n', '10', HEX + '/glift', path, spec_], capture_output=True, text=True,
                       env={'OMP_NUM_THREADS': '1', 'PATH': '/usr/bin:/bin:/usr/local/bin'})
    mm = re.search(r'COST (\d+)', r.stdout)
    return int(mm.group(1)) if mm else -1

# failing (source, target) pairs from the dump of the initial design (verbose 2 output of glift)
pairs = {}
for line in open(dumpf):
    if line.startswith('  src'):
        t = line.split(); s = int(t[1].rstrip(':')); v = int(t[2][1:])
        pairs.setdefault((s, v), 1)
pair_list = list(pairs.keys())
random.Random(seed).shuffle(pair_list)
pair_list = pair_list[:max_pairs]
print(f'failing pairs in dump: {len(pairs)}, using {len(pair_list)}', flush=True)

# candidate sets J(x,t) over points u
cand = set(axis_idx.tolist())
J = []
for (x, t) in pair_list:
    dx = bfs(x); dt = bfs(t)
    du = np.arange(N)
    dl = phi[:N]                               # delta(u) for points u
    ok = (dx[du] + dt[dl] <= 6) | (dx[dl] + dt[du] <= 6)
    Jx = np.nonzero(ok)[0]
    J.append(Jx)
    cand.update(Jx.tolist())
print(f'candidate points: {len(cand)} (axis {len(axis_idx)}), mean |J| {np.mean([len(j) for j in J]):.1f}', flush=True)
cand = np.array(sorted(cand))

F1_0, F2_0 = F1.copy(), F2.copy()
cur_path = f'{outp}_cur.txt'
write(F1, F2, cur_path)
base_cost = glift(cur_path, 'r:64:1')
print(f'initial COST r:64:1 = {base_cost}', flush=True)
cur = base_cost
changed = set()
t0 = time.time(); it = 0; acc = 0
rr = random.Random(seed + 99)
while time.time() - t0 < budget and cur > 0:
    it += 1
    if rr.random() < 0.5 and len(J):
        Jx = J[rr.randrange(len(J))]
        u = int(Jx[rr.randrange(len(Jx))]) if len(Jx) else int(cand[rr.randrange(len(cand))])
    else:
        u = int(cand[rr.randrange(len(cand))])
    old = (F1[u], F2[u])
    mv = rr.random()
    if mv < 0.4:
        F1[u] = rr.randrange(m)
    elif mv < 0.8:
        F2[u] = rr.randrange(m)
    else:
        F1[u] = rr.randrange(m); F2[u] = rr.randrange(m)
    if (F1[u], F2[u]) == old:
        continue
    write(F1, F2, cur_path + '.tmp')
    new = glift(cur_path + '.tmp', 'r:64:1')
    if 0 <= new <= cur:
        cur = new; acc += 1
        if (F1[u], F2[u]) != (F1_0[u], F2_0[u]): changed.add(u)
        else: changed.discard(u)
    else:
        F1[u], F2[u] = old
    if it % 25 == 0:
        print(f'it {it} acc {acc} cost {cur} changed {len(changed)} t {time.time()-t0:.0f}s', flush=True)
# final file
final = f'{outp}_final.txt'
write(F1, F2, final)
print(f'done it {it} acc {acc} cost(r:64:1) {cur} points changed {len(changed)} (nonzero diff {int(np.sum((F1!=F1_0)|(F2!=F2_0)))})', flush=True)
np.save(f'{outp}_final_f.npy', np.stack([F1, F2]))

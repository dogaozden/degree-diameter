"""Sample (4,3) charts that cover both diagonals and keep the ones with fewest singular patterns.
For a pair of point configurations (w_s), (b_s) (orbit representatives of diag_exhaust.py), the joint search
(diag_joint_many) lists choices of per-letter (A-mask, B-mask) pairs whose unions cover both diagonals; every star
collineation sigma_s realising the chosen pair, lifted to any A_s with A_s w_s = b_s (shear/scale freedom), gives a chart
covering both diagonals.  We sample sigma_s and the shear/scale at random, evaluate singular patterns and pencils with
chart_eval (same cost code as chart_anneal), and keep the best charts (written in chart_anneal format, gauge A_0 = I).
usage: python3 diag_charts.py WNAME BNAME NSOL SAMPLES_PER_SOL SEED outprefix"""
import importlib.util, sys, subprocess, random, itertools, os
spec = importlib.util.spec_from_file_location('de', 'diag_exhaust3.py'); de = importlib.util.module_from_spec(spec)
wn, bn, nsol, nsamp, seed, outp = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
sys.argv = ['x']; spec.loader.exec_module(de)
q = de.q; W = de.REPS[wn]; B = de.REPS[bn]; rng = random.Random(seed)
need = (de.FULL & ~de.edges_mask(W), de.FULL & ~de.edges_mask(B))
inp = '%d %d\n' % need; tables = []
for s in range(4):
    bw, bb = de.complement_basis(W[s]), de.complement_basis(B[s])
    lineA = {}; lineB = {}
    for d in de.PG2:
        v = [sum(c * x[i] for c, x in zip(d, bw)) % q for i in range(4)]; lineA[d] = de.line_mask(W[s], v)
        v = [sum(c * x[i] for c, x in zip(d, bb)) % q for i in range(4)]; lineB[d] = de.line_mask(B[s], v)
    others = [t for t in range(4) if t != s]
    dirE = [de.star_coords(W[s], bw, W[t]) for t in others]; dirEp = [de.star_coords(B[s], bb, B[t]) for t in others]
    real = {}
    for M, perm in zip(de.MATS, de.PERMS):
        inv = {perm[i]: de.PG2[i] for i in range(len(de.PG2))}
        mA = 0; mB = 0
        for d in dirEp: mA |= lineA[inv[d]]
        for d in dirE: mB |= lineB[perm[de.P2I[d]]]
        real.setdefault((mA & need[0], mB & need[1]), []).append(M)
    Am = sorted({a for a, b in real}); Bm = sorted({b for a, b in real})
    ia = {a: i for i, a in enumerate(Am)}; ib = {b: i for i, b in enumerate(Bm)}
    inp += '%d\n%s\n%d\n%s\n%d\n' % (len(Am), ' '.join(map(str, Am)), len(Bm), ' '.join(map(str, Bm)), len(real))
    inp += ''.join('%d %d\n' % (ia[a], ib[b]) for a, b in sorted(real))
    tables.append((Am, Bm, real, bw, bb))
env = dict(os.environ, MAXSOL=str(nsol))
out = subprocess.run(['./diag_joint_many'], input=inp, capture_output=True, text=True, env=env).stdout
sols = [list(map(int, l.split()[1:])) for l in out.splitlines() if l.startswith('SOL')]
print('configuration', wn, bn, 'solutions found', len(sols), flush=True)
def matmul(X, Y): return [[sum(X[i][t] * Y[t][j] for t in range(len(Y))) % q for j in range(len(Y[0]))] for i in range(len(X))]
def inv4(M):
    n = 4; T = [list(M[r]) + [int(r == c) for c in range(n)] for r in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if T[r][c] % q); T[c], T[p] = T[p], T[c]
        iv = pow(T[c][c], q - 2, q); T[c] = [(x * iv) % q for x in T[c]]
        for r in range(n):
            if r != c and T[r][c] % q:
                fct = T[r][c]; T[r] = [(x - fct * y) % q for x, y in zip(T[r], T[c])]
    return [row[n:] for row in T]
def lift(s, M, lam, phi):
    Am, Bm, real, bw, bb = tables[s]
    src = [list(W[s])] + [list(v) for v in bw]; dst = [list(B[s])]
    for i in range(3):
        img = [sum(M[j][i] * bb[j][r] for j in range(3)) % q for r in range(4)]
        dst.append([(lam * img[r] + phi[i] * B[s][r]) % q for r in range(4)])
    S = [[src[c][r] for c in range(4)] for r in range(4)]; Dm = [[dst[c][r] for c in range(4)] for r in range(4)]
    return matmul(Dm, inv4(S))
charts = []
for sol in sols:
    iA, iB = sol[:4], sol[4:]
    lists = [tables[s][2][(tables[s][0][iA[s]], tables[s][1][iB[s]])] for s in range(4)]
    for t in range(nsamp):
        As = [lift(s, rng.choice(lists[s]), rng.randint(1, q - 1), [rng.randrange(q) for _ in range(3)]) for s in range(4)]
        G = inv4(As[0]); As = [matmul(A, G) for A in As]
        charts.append(As)
txt = ''
for As in charts:
    txt += ''.join(' '.join(str(x) for row in A for x in row) + '\n' for A in As)
    txt += ''.join(' '.join(map(str, B[s])) + '\n' for s in range(4))
res = subprocess.run(['./chart_eval', '../../tables/gf3.txt', '4'], input=txt, capture_output=True, text=True).stdout.split('\n')
scored = []
for As, line in zip(charts, res):
    s_, p_, d_ = map(int, line.split()); assert d_ == 0, 'diagonal not covered?!'
    if p_ == 0: scored.append((s_, As))
scored.sort(key=lambda x: x[0])
hist = {}
for s_, _ in scored: hist[s_] = hist.get(s_, 0) + 1
print('pencil-complete charts:', len(scored), 'of', len(charts), '; singular histogram (low end):', sorted(hist.items())[:8], flush=True)
for r, (s_, As) in enumerate(scored[:5]):
    with open('%s_%d_s%d.txt' % (outp, r, s_), 'w') as fo:
        fo.write(''.join(' '.join(str(x) for row in A for x in row) + ' \n' for A in As))
        fo.write(''.join(' '.join(map(str, B[s])) + ' \n' for s in range(4)))
print('best singular', scored[0][0] if scored else None)

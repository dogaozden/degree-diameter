"""Reconstruct an explicit (4,3) chart covering both diagonals from the joint search (diag_exhaust3.py + diag_joint):
pick, for each letter s, a star collineation sigma_s realising the found (A-mask, B-mask) pair, lift it to A_s with
A_s w_s = b_s, gauge A_0 = I (A_s -> A_s A_0^-1), write the chart (chart_anneal format) and re-check it with chartlib.
usage: python3 build_diag_chart.py WNAME BNAME out_chart.txt"""
import importlib.util, sys, subprocess, itertools
spec = importlib.util.spec_from_file_location('de', 'diag_exhaust3.py'); de = importlib.util.module_from_spec(spec)
wn, bn, outp = sys.argv[1], sys.argv[2], sys.argv[3]
sys.argv = ['x']; spec.loader.exec_module(de)
q = de.q; W = de.REPS[wn]; B = de.REPS[bn]
need = (de.FULL & ~de.edges_mask(W), de.FULL & ~de.edges_mask(B))
# rerun the joint search to get mask indices
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
        real.setdefault((mA & need[0], mB & need[1]), M)
    Am = sorted({a for a, b in real}); Bm = sorted({b for a, b in real})
    ia = {a: i for i, a in enumerate(Am)}; ib = {b: i for i, b in enumerate(Bm)}
    inp += '%d\n%s\n%d\n%s\n%d\n' % (len(Am), ' '.join(map(str, Am)), len(Bm), ' '.join(map(str, Bm)), len(real))
    inp += ''.join('%d %d\n' % (ia[a], ib[b]) for a, b in sorted(real))
    tables.append((Am, Bm, real, bw, bb))
out = subprocess.run(['./diag_joint'], input=inp, capture_output=True, text=True).stdout.strip()
print(out)
f = out.split()
iA = list(map(int, f[2:6])); iB = list(map(int, f[7:11]))
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
As = []
for s in range(4):
    Am, Bm, real, bw, bb = tables[s]
    M = real[(Am[iA[s]], Bm[iB[s]])]
    # columns: A_s w_s = b_s, A_s bw_i = sum_j M[j][i] bb_j
    src = [list(W[s])] + [list(v) for v in bw]; dst = [list(B[s])]
    for i in range(3): dst.append([sum(M[j][i] * bb[j][r] for j in range(3)) % q for r in range(4)])
    S = [[src[c][r] for c in range(4)] for r in range(4)]; Dm = [[dst[c][r] for c in range(4)] for r in range(4)]
    As.append(matmul(Dm, inv4(S)))
A0i = inv4(As[0]); As = [matmul(A, A0i) for A in As]
with open(outp, 'w') as fo:
    for A in As: fo.write(' '.join(str(x) for row in A for x in row) + ' \n')
    for s in range(4): fo.write(' '.join(str(x) for x in B[s]) + ' \n')
print('wrote', outp)

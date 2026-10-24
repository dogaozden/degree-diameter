"""All distinct labelled singular sets of (4,3) charts that cover both diagonals (Proposition 12(c)): from the 1,152
normal-form charts, plus all 24 relabellings of the letters; writes one ctrl_search flags file per distinct set to
../flags43/s<i>.flags (pencils complete and both diagonals covered in every case)."""
import sys, itertools, os
sys.argv = ['diag_charts.py', 'tetra', 'tetra', '1000', '1', '1', '/dev/null']
src = open('diag_charts.py').read(); src = src[:src.index('charts = []')]
ns = {'__name__': 'x'}; exec(compile(src, 'diag_charts_head', 'exec'), ns)
sols, tables, lift, inv4, B, de = ns['sols'], ns['tables'], ns['lift'], ns['inv4'], ns['B'], ns['de']
W = de.REPS['tetra']; q = 3; k = 4
def mv(X, v): return [sum(X[i][j] * v[j] for j in range(4)) % q for i in range(4)]
sets = {}
for sol in sols:
    iA, iB = sol[:4], sol[4:]
    per = []
    for s in range(4):
        rep = {}
        for M in tables[s][2][(tables[s][0][iA[s]], tables[s][1][iB[s]])]:
            A = lift(s, M, 1, [0, 0, 0]); Ai = inv4(A)
            U = {t: de.mask(de.span_pts([mv(Ai, B[s]), mv(Ai, B[t])])) for t in range(4) if t != s}
            V = {t: de.mask(de.span_pts([mv(A, W[s]), mv(A, W[t])])) for t in range(4) if t != s}
            rep[(tuple(sorted(U.items())), tuple(sorted(V.items())))] = (U, V, A)
        per.append(list(rep.values()))
    for combo in itertools.product(*per):
        U = [c[0] for c in combo]; V = [c[1] for c in combo]
        sA = frozenset(p for p in itertools.product(range(4), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3] and U[p[1]][p[0]] & U[p[2]][p[3]])
        sB = frozenset(p for p in itertools.product(range(4), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3] and V[p[1]][p[0]] & V[p[2]][p[3]])
        for perm in itertools.permutations(range(4)):
            key = (frozenset(tuple(perm[x] for x in p) for p in sA), frozenset(tuple(perm[x] for x in p) for p in sB))
            if key not in sets: sets[key] = (combo, perm)
os.makedirs('../flags43', exist_ok=True)
def matmul(X, Y): return [[sum(X[i][t] * Y[t][j] for t in range(4)) % q for j in range(4)] for i in range(4)]
for i, (sA, sB) in enumerate(sorted(sets, key=lambda x: (sorted(x[0]), sorted(x[1])))):
    combo, perm = sets[(sA, sB)]
    As = [None] * 4; bs = [None] * 4
    for c in range(4): As[perm[c]] = combo[c][2]; bs[perm[c]] = B[c]          # relabel: new letter perm[c] = old letter c
    G = inv4(As[0]); As = [matmul(A, G) for A in As]
    with open('../flags43/s%03d.txt' % i, 'w') as f:
        f.write(''.join(' '.join(str(x) for row in A for x in row) + ' \n' for A in As))
        f.write(''.join(' '.join(map(str, b)) + ' \n' for b in bs))
    with open('../flags43/s%03d.flags' % i, 'w') as f:
        f.write('4\n')
        for S in (sA, sB): f.write(' '.join(str(int(p in S)) for p in itertools.product(range(4), repeat=4)) + '\n')
        for _ in range(2): f.write(' '.join(str(int(i_ != j_)) for i_ in range(4) for j_ in range(4)) + '\n')
        f.write('1 1\n')
print('distinct labelled singular sets:', len(sets), 'sizes', sorted({(len(a), len(b)) for a, b in sets}))

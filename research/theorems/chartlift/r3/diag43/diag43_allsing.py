"""Exhaustive version of the (4,3) singular-pattern count: for every one of the 72 diagonal-covering mask solutions
(tetrahedron/tetrahedron normal form) and EVERY star collineation realising each letter's mask pair, build the chart
(shear 0; shears do not change any D = 5 condition, Lemma 5) and evaluate singular patterns, pencils and diagonals with
chart_eval.  Charts are reduced per letter to distinct labelled (U-lines, V-lines) data first."""
import sys, subprocess, itertools
sys.argv = ['diag_charts.py', 'tetra', 'tetra', '1000', '1', '1', '/dev/null']
src = open('diag_charts.py').read(); src = src[:src.index('charts = []')]
ns = {'__name__': 'x'}; exec(compile(src, 'diag_charts_head', 'exec'), ns)
sols, tables, lift, inv4, matmul, B, de = ns['sols'], ns['tables'], ns['lift'], ns['inv4'], ns['matmul'], ns['B'], ns['de']
W = de.REPS['tetra']; q = 3
def lines_of(s, M):
    """labelled U-lines and V-lines (as point masks) of letter s under collineation M."""
    Am, Bm, real, bw, bb = tables[s]
    A = lift(s, M, 1, [0, 0, 0])
    Ai = inv4(A)
    mv = lambda X, v: [sum(X[i][j] * v[j] for j in range(4)) % q for i in range(4)]
    U = tuple(de.mask(de.span_pts([mv(Ai, B[s]), mv(Ai, B[t])])) for t in range(4) if t != s)
    V = tuple(de.mask(de.span_pts([mv(A, W[s]), mv(A, W[t])])) for t in range(4) if t != s)
    return (U, V), A
total = 0; stats = {}
for sol in sols:
    iA, iB = sol[:4], sol[4:]
    per = []
    for s in range(4):
        Ms = tables[s][2][(tables[s][0][iA[s]], tables[s][1][iB[s]])]
        rep = {}
        for M in Ms:
            key, A = lines_of(s, M)
            rep.setdefault(key, A)
        per.append(list(rep.values()))
    txt = ''
    for combo in itertools.product(*per):
        G = inv4(combo[0]); As = [matmul(A, G) for A in combo]
        txt += ''.join(' '.join(str(x) for row in A for x in row) + '\n' for A in As) + ''.join(' '.join(map(str, B[s])) + '\n' for s in range(4))
        total += 1
    res = subprocess.run(['./chart_eval', '../../tables/gf3.txt', '4'], input=txt, capture_output=True, text=True).stdout.split('\n')
    for r in res:
        if r.strip(): stats[r.strip()] = stats.get(r.strip(), 0) + 1
print('solutions', len(sols), 'charts evaluated (distinct labelled line data per letter, all combinations):', total)
print('(singular, pencil-miss vectors, diagonal-miss vectors) -> count:', stats)

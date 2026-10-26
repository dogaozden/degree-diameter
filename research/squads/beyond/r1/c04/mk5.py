#!/usr/bin/env python3
"""F_5 versions of chart_patterns.py and build_lift_general.py.
  mk5.py patterns CHART OUT   : 216 lines 'side i1 i2 i3 i4 rank' (same formulas as chart_patterns.py)
  mk5.py build CTRL CHART OUT : route-chart lift over F_5 of a controller edge list 'a b colour' (a, b in 0..m-1 per
                                side, B vertices offset by m); fibre F_5^4, degree 20, 2*m*625 vertices."""
import sys, itertools
P = 5
INV = {1: 1, 2: 3, 3: 2, 4: 4}

def load(path):
    v = [int(x) for x in open(path).read().split()]
    A = [[v[16 * i + 4 * r: 16 * i + 4 * r + 4] for r in range(4)] for i in range(4)]
    b = [tuple(v[64 + 4 * i: 64 + 4 * i + 4]) for i in range(4)]
    return A, b

def mv(M, x):
    return tuple(sum(M[r][c] * x[c] for c in range(4)) % P for r in range(4))

def minv(M):
    X = [list(M[r]) + [int(r == c) for c in range(4)] for r in range(4)]
    for col in range(4):
        piv = next((r for r in range(col, 4) if X[r][col] % P), None)
        if piv is None: return None
        X[col], X[piv] = X[piv], X[col]
        iv = INV[X[col][col] % P]; X[col] = [x * iv % P for x in X[col]]
        for r in range(4):
            if r != col and X[r][col] % P:
                f = X[r][col]; X[r] = [(x - f * y) % P for x, y in zip(X[r], X[col])]
    return [row[4:] for row in X]

def rank(vs):
    a = [list(v) for v in vs]; r = 0
    for col in range(4):
        p = next((i for i in range(r, len(a)) if a[i][col] % P), None)
        if p is None: continue
        a[r], a[p] = a[p], a[r]; iv = INV[a[r][col] % P]; a[r] = [x * iv % P for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col] % P:
                f = a[i][col]; a[i] = [(x - f * y) % P for x, y in zip(a[i], a[r])]
        r += 1
    return r

def patterns(chart, out):
    A, b = load(chart); Ai = [minv(M) for M in A]
    assert all(Ai), 'A_i singular'
    nsing = 0
    with open(out, 'w') as f:
        for i1, i2, i3, i4 in itertools.product(range(4), repeat=4):
            if i1 == i2 or i2 == i3 or i3 == i4: continue
            rA = rank([mv(Ai[i2], b[i1]), mv(Ai[i2], b[i2]), mv(Ai[i3], b[i3]), mv(Ai[i3], b[i4])])
            rB = rank([mv(A[i2], mv(Ai[i1], b[i1])), b[i2], b[i3], mv(A[i3], mv(Ai[i4], b[i4]))])
            f.write(f"A {i1} {i2} {i3} {i4} {rA}\nB {i1} {i2} {i3} {i4} {rB}\n")
            nsing += (rA < 4) + (rB < 4)
    print('singular patterns (of 216):', nsing)

def vid(x):
    return x[0] + 5 * x[1] + 25 * x[2] + 125 * x[3]

def build(ctrl, chart, out):
    A, b = load(chart)
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    m = max(max(a, bb) for a, bb, c in rows) + 1
    assert len(rows) == 4 * m, 'controller must be 4-regular on m+m vertices'
    for side in (0, 1):
        seen = set()
        for r in rows:
            assert (r[side], r[2]) not in seen, 'colouring not proper'; seen.add((r[side], r[2]))
    fib = list(itertools.product(range(P), repeat=4))
    E = []
    for a, bb, c in rows:
        for x in fib:
            y0 = mv(A[c], x)
            for lam in range(P):
                y = tuple((p + lam * q) % P for p, q in zip(y0, b[c]))
                E.append((a * 625 + vid(x), m * 625 + bb * 625 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    with open(out, 'w') as f:
        f.write(f"{2 * m * 625}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('controller m =', m, 'vertices', 2 * m * 625, 'edges', len(E))

if __name__ == '__main__':
    if sys.argv[1] == 'patterns': patterns(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == 'build': build(sys.argv[2], sys.argv[3], sys.argv[4])

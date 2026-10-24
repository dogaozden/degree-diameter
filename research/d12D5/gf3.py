#!/usr/bin/env python3
"""F_3^4 helpers for the (12,5) route-chart lift (4 letters x 3 scalars).

Chart text format (chart3.c): 4 lines of 16 entries (A_0..A_3 row-major), then 4 lines b_0..b_3; entries in {0,1,2}.
Lift of a properly 4-edge-coloured 4-regular bipartite controller (lines "a b c": A-vertex a, B-vertex b, colour c):
    (a, x)_A -- (b, A_c x + lam b_c)_B,  lam in F_3,  so the lift is 12-regular, bipartite, on 2 * 81 * m vertices.
Vertex numbering: A-vertex (a, x) -> a * 81 + id(x), B-vertex (b, y) -> 81 m + b * 81 + id(y), id(x) = x0 + 3 x1 + 9 x2 + 27 x3.

usage:
  python3 gf3.py relabel CHART PREFIX         24 colour relabellings: PREFIX_qXX.txt (pattern tables), PREFIX_chart_qXX.txt,
                                              PREFIX_perms.txt  (relabelling q: controller colour c uses chart letter p[c])
  python3 gf3.py lift CONTROLLER CHART OUT    write the lift as an apsp.c edge list (first line n, then "u v")
"""
import sys, itertools

def load_chart(fn):
    rows = [list(map(int, l.split())) for l in open(fn) if l.strip()]
    A = [[r[4 * i:4 * i + 4] for i in range(4)] for r in rows[:4]]
    b = [tuple(x % 3 for x in r) for r in rows[4:8]]
    return [[[x % 3 for x in row] for row in M] for M in A], b

def mat_vec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(4)) % 3 for r in range(4))

def mat_mul(M, N):
    return [[sum(M[r][k] * N[k][c] for k in range(4)) % 3 for c in range(4)] for r in range(4)]

def mat_inv(M):
    X = [list(M[r]) + [int(r == c) for c in range(4)] for r in range(4)]
    for col in range(4):
        piv = next((r for r in range(col, 4) if X[r][col]), None)
        if piv is None:
            return None
        X[col], X[piv] = X[piv], X[col]
        if X[col][col] == 2:
            X[col] = [(2 * x) % 3 for x in X[col]]
        for r in range(4):
            if r != col and X[r][col]:
                f = X[r][col]
                X[r] = [(x - f * y) % 3 for x, y in zip(X[r], X[col])]
    return [row[4:] for row in X]

def rank(vecs):
    rows = [list(v) for v in vecs]; r = 0
    for col in range(4):
        piv = next((i for i in range(r, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        if rows[r][col] == 2:
            rows[r] = [(2 * x) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def pattern_ranks(A, b):
    Ai = [mat_inv(M) for M in A]
    r = {}
    for (i1, i2, i3, i4) in itertools.product(range(4), repeat=4):
        if i1 == i2 or i2 == i3 or i3 == i4:
            continue
        r[('A', i1, i2, i3, i4)] = rank([mat_vec(Ai[i2], b[i1]), mat_vec(Ai[i2], b[i2]), mat_vec(Ai[i3], b[i3]), mat_vec(Ai[i3], b[i4])])
        r[('B', i1, i2, i3, i4)] = rank([mat_vec(A[i2], mat_vec(Ai[i1], b[i1])), b[i2], b[i3], mat_vec(A[i3], mat_vec(Ai[i4], b[i4]))])
    return r

def relabel(chart, out):
    A, b = load_chart(chart)
    r = pattern_ranks(A, b)
    with open(out + '_perms.txt', 'w') as g:
        for K, p in enumerate(itertools.permutations(range(4))):
            g.write("q%02d %s\n" % (K, p))
            with open(out + '_q%02d.txt' % K, 'w') as f:
                for s in 'AB':
                    for q in itertools.product(range(4), repeat=4):
                        if q[0] == q[1] or q[1] == q[2] or q[2] == q[3]:
                            continue
                        f.write("%s %d %d %d %d %d\n" % ((s,) + q + (r[(s, p[q[0]], p[q[1]], p[q[2]], p[q[3]])],)))
            G = mat_inv(A[p[0]])
            with open(out + '_chart_q%02d.txt' % K, 'w') as f:
                for c in range(4):
                    M = mat_mul(A[p[c]], G)
                    f.write(' '.join(str(M[i][j]) for i in range(4) for j in range(4)) + '\n')
                for c in range(4):
                    f.write(' '.join(map(str, b[p[c]])) + '\n')
    print('singular patterns', sum(v < 4 for v in r.values()), '; wrote 24 relabellings with prefix', out)

def vid(v):
    return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]

def lift(ctrl, chart, out):
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    m = max(r[0] for r in rows) + 1
    assert len(rows) == 4 * m and max(r[1] for r in rows) + 1 == m
    for side in (0, 1):                      # the colouring must be proper on both sides
        seen = set()
        for r in rows:
            key = (r[side], r[2]); assert key not in seen, 'colouring not proper'; seen.add(key)
    A, b = load_chart(chart)
    vecs = list(itertools.product(range(3), repeat=4)); nA = m * 81
    E = []
    for a, bb, c in rows:
        for x in vecs:
            y0 = mat_vec(A[c], x)
            for lam in range(3):
                y = tuple((p + lam * q) % 3 for p, q in zip(y0, b[c]))
                E.append((a * 81 + vid(x), nA + bb * 81 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    with open(out, 'w') as f:
        f.write(f"{2 * nA}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('controller m =', m, 'lift vertices', 2 * nA, 'edges', len(E))

if __name__ == '__main__':
    if sys.argv[1] == 'relabel':
        relabel(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == 'lift':
        lift(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        print(__doc__)

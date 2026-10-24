"""Check the projective reformulation (CHART_LIFTS.md, Lemmas 2-4) against the direct walk computation (chartlib).
  U(j;i) = A_j^-1 <b_i, b_j>  (line through w_j = A_j^-1 b_j),   V(j;i) = A_j <w_i, w_j>  (line through b_j).
  A-pattern (i1,i2,i3,i4) singular  <=>  U(i2;i1) and U(i3;i4) meet (or one is not a line).
  B-pattern singular                 <=>  V(i2;i1) and V(i3;i4) meet.
  A-pencil (i,j) complete <=> the planes <b_i,b_j,V(i;t)>, <b_i,b_j,V(j;t)>, <b_i,b_j,b_t> are all q+1 planes on <b_i,b_j>.
  B-pencil (i,j) complete <=> the same in the A-space with U, w.
  Diagonal of side A covered <=> the lines <w_s,w_t> and U(s;t) cover PG(3,q); side B: <b_s,b_t> and V(s;t).
usage: python3 geometry_check.py CHART q k [CHART q k ...]"""
import sys, itertools
from chartlib import read_chart_txt

def check(path, q, k):
    ch = read_chart_txt(path, q, k); F = ch.F
    pts = lambda vecs: frozenset(F.canon(v) for v in F.span(vecs, 4) if any(v))
    U = {(j, i): pts([F.matvec(ch.Ai[j], ch.b[i]), ch.w[j]]) for j in range(k) for i in range(k) if i != j}
    V = {(j, i): pts([ch.b[j], F.matvec(ch.A[j], ch.w[i])]) for j in range(k) for i in range(k) if i != j}
    isline = lambda L: len(L) == q + 1
    direct = {(s, p) for s, p, r in ch.singular_patterns()}
    geo = set()
    for p in ch.nb_patterns(4):
        i1, i2, i3, i4 = p
        for s, L in (('A', U), ('B', V)):
            a, b_ = L[(i2, i1)], L[(i3, i4)]
            if not (isline(a) and isline(b_)) or (a & b_): geo.add((s, p))
    ok_sing = direct == geo
    # pencils
    ok_pen = True; npl = 0
    for s in 'AB':
        for i in range(k):
            for j in range(k):
                if i == j: continue
                if s == 'A':
                    base = [ch.b[i], ch.b[j]]; extra = [F.matvec(ch.A[i], ch.w[t]) for t in range(k)] + list(ch.b) + [F.matvec(ch.A[j], ch.w[t]) for t in range(k)]
                else:
                    base = [ch.w[i], ch.w[j]]; extra = [F.matvec(ch.Ai[i], ch.b[t]) for t in range(k)] + list(ch.w) + [F.matvec(ch.Ai[j], ch.b[t]) for t in range(k)]
                planes = {pts(base + [z]) for z in extra if F.rank(base + [z]) == 3}
                geo_ok = F.rank(base) == 2 and len(planes) == q + 1
                if geo_ok != ch.pencil(s, i, j)[1]: ok_pen = False
                npl += geo_ok
    # diagonal
    allpts = pts([(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)])
    covA = set().union(*U.values(), *[pts([ch.w[s], ch.w[t]]) for s in range(k) for t in range(k)])
    covB = set().union(*V.values(), *[pts([ch.b[s], ch.b[t]]) for s in range(k) for t in range(k)])
    ok_diag = (covA == allpts) == ch.diagonal('A')[1] and (covB == allpts) == ch.diagonal('B')[1]
    inter = sum(1 for (j, i), (l, t) in itertools.combinations(U, 2) if j != l and U[(j, i)] & U[(l, t)])
    interV = sum(1 for (j, i), (l, t) in itertools.combinations(V, 2) if j != l and V[(j, i)] & V[(l, t)])
    print('%-40s q=%d k=%d singular %3d (direct) = geometric: %s | meeting U-pairs %d, V-pairs %d | complete pencils %d/%d, geometric = direct: %s | diagonal geometric = direct: %s'
          % (path, q, k, len(direct), ok_sing, inter, interV, npl, 2 * k * (k - 1), ok_pen, ok_diag))
    return ok_sing and ok_pen and ok_diag

args = sys.argv[1:]
allok = all(check(args[t], int(args[t + 1]), int(args[t + 2])) for t in range(0, len(args), 3))
print('ALL AGREE' if allok else 'MISMATCH')

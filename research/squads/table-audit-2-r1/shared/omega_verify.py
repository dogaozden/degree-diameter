"""Independent structural check (table-audit): is EDGES exactly Gomez's Omega H(q) (thesis 1986, Fig. 2.21 a/b) for
the labelling LAB?  Re-derives the wiring from the figure in Python (does not use omega_model.h):
  copy c = 5B+i holds base vertex v (points 0..n-1, lines n..2n-1) at id c*2n+v, with exactly the base edges;
  row t of copy c marks point P_c[t] and line L_c[t]; the inner one is the line if INNER[B]=='L' else the point;
  hub (t,k) / (t,kbar) at id 5*alpha*2n + 10t + 5bar + k;
  type a: (t,k) on the inner marks of copies k-1, k+1 and (t,kbar) on the outer marks of copies k+2, k+3 (circle);
  type b: (t,k) on the outer marks of copies k+3, k+4 and (t,kbar) on the inner marks of copies k-1, k+1.
Also checks that every P_c, L_c is a bijection.  usage: omega_verify.py HEX TYPES INNER LAB EDGES"""
import sys
hexp, types, inner, labp, edgep = sys.argv[1:6]
with open(hexp) as f:
    nb = int(f.readline()); base = [tuple(map(int, l.split())) for l in f if l.strip()]
n = nb // 2; A = len(types); C = 5 * A
vals = list(map(int, open(labp).read().split()))
assert len(vals) == 2 * C * n
P = [vals[c * n:(c + 1) * n] for c in range(C)]
L = [vals[C * n + c * n:C * n + (c + 1) * n] for c in range(C)]
for c in range(C):
    assert sorted(P[c]) == list(range(n)) and sorted(L[c]) == list(range(n)), "not a bijection"
want = set()
for c in range(C):
    for u, v in base:
        want.add((min(c * nb + u, c * nb + v), max(c * nb + u, c * nb + v)))
H0 = C * nb
def mark(c, t, which):            # which: 'I' or 'O'
    B = c // 5
    line_is_inner = inner[B] == 'L'
    use_line = (which == 'I') == line_is_inner
    return c * nb + (n + L[c][t] if use_line else P[c][t])
for B, ty in enumerate(types):
    for t in range(n):
        for k in range(5):
            if ty == 'a':
                ends = [((t, 0, k), (k - 1) % 5, 'I'), ((t, 0, k), (k + 1) % 5, 'I'),
                        ((t, 1, k), (k + 2) % 5, 'O'), ((t, 1, k), (k + 3) % 5, 'O')]
            else:
                ends = [((t, 0, k), (k + 3) % 5, 'O'), ((t, 0, k), (k + 4) % 5, 'O'),
                        ((t, 1, k), (k - 1) % 5, 'I'), ((t, 1, k), (k + 1) % 5, 'I')]
            for (tt, bar, kk), i, w in ends:
                h = H0 + 10 * tt + 5 * bar + kk
                x = mark(5 * B + i, tt, w)
                want.add((min(h, x), max(h, x)))
with open(edgep) as f:
    nv = int(f.readline()); got = set()
    for l in f:
        if l.strip():
            u, v = map(int, l.split()); got.add((min(u, v), max(u, v)))
assert nv == H0 + 10 * n, (nv, H0 + 10 * n)
print(f'q-hexagon n={n} types={types} inner={inner}: vertices {nv} (= 5(alpha+1)|H| = {5 * (A + 1) * nb}), '
      f'edges expected {len(want)}, in file {len(got)}, equal: {want == got}')
sys.exit(0 if want == got else 1)

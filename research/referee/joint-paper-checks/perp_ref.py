"""Sanity check of Lemma 7.20 at q=7 on fixed-point-free elements h of the SL(3,7) subgroup of G_2(7) (Fact 2.3):
|Perp(h)| should be at most 4144."""
import itertools, random
q = 7
pts = []
for lead in range(7):
    for rest in itertools.product(range(q), repeat=6 - lead):
        v = (0,) * lead + (1,) + rest
        if (v[0]*v[4] + v[1]*v[5] + v[2]*v[6] - v[3]*v[3]) % q == 0: pts.append(v)
assert len(pts) == 19608
def b(x, y): return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q
def mat_inv_T(A):
    import sympy
    M = sympy.Matrix(A); Mi = M.inv_mod(q); return [[int(Mi[j, i]) % q for j in range(3)] for i in range(3)]
def apply(A, AiT, x):
    v, a, w = x[:3], x[3], x[4:]
    Av = [sum(A[i][k]*v[k] for k in range(3)) % q for i in range(3)]
    Bw = [sum(AiT[i][k]*w[k] for k in range(3)) % q for i in range(3)]
    return tuple(Av) + (a,) + tuple(Bw)
def norm(v):
    for c in v:
        if c: ic = pow(c, q - 2, q); return tuple((ic*t) % q for t in v)
random.seed(5)
import sympy
found = 0; worst = 0; tried = 0
while found < 12 and tried < 4000:
    tried += 1
    A = [[random.randrange(q) for _ in range(3)] for _ in range(3)]
    d = int(sympy.Matrix(A).det()) % q
    if d == 0: continue
    A[0] = [(pow(d, q - 2, q) * t) % q for t in A[0]]
    AiT = mat_inv_T(A)
    imgs = [norm(apply(A, AiT, x)) for x in pts]
    if any(imgs[i] == pts[i] for i in range(len(pts))): continue
    perp = sum(1 for i, x in enumerate(pts) if b(x, imgs[i]) == 0)
    worst = max(worst, perp); found += 1
print(f"Lemma 7.20 sanity check, q=7: {found} fixed-point-free elements of SL(3,7) inside G2(7); max |Perp(h)| = {worst} (bound 4144)")

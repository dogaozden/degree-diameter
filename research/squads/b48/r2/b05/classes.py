# Edge orbit class of each seed edge: edge (g,A)~(h,B) has class s = h*g^-1 in S (right-multiplication orbits).
import sys
m, k, r = 91, 12, 25
N = m * k
def el(i): return (i // k, i % k)            # index a*k + j (build_haar2 Meta)
def idx(a, j): return (a % m) * k + (j % k)
def mul(g, h):
    a, j = g; b, l = h
    return ((a + pow(r, j, m) * b) % m, (j + l) % k)
def inv(g):
    a, j = g
    rinv = pow(r, (-j) % 0 if False else 0, m)  # placeholder
    rj_inv = pow(pow(r, j, m), -1, m)
    return ((-rj_inv * a) % m, (-j) % k)
lines = open('/home/user/degree-diameter/research/squads/b48/seeds/haar_meta_91_12_25_n2184.edges').read().split('\n')
n = int(lines[0])
E = []
for ln in lines[1:]:
    if ln.strip():
        u, v = map(int, ln.split()); E.append((u, v))
assert len(E) == 2184 * 2, len(E)
# normalise: side A = u < N
out = []
S = {}
for u, v in E:
    assert u < N <= v
    g = el(u); h = el(v - N)
    s = mul(h, inv(g))
    S.setdefault(idx(*s), 0)
    S[idx(*s)] += 1
    out.append((u, v, idx(*s)))
print('classes (s index: count):', S, file=sys.stderr)
with open('/home/user/degree-diameter/research/squads/b48/r2/b05/classes.txt', 'w') as f:
    f.write('%d\n' % n)
    for u, v, c in out:
        f.write('%d %d %d\n' % (u, v, c))

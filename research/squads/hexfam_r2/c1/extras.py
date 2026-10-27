import sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from lib import *
q = 9
F = G.fmul
INV = G.INV
def torus(a, b):
    c = G.fmul(INV[a], INV[b])  # c = 1/(ab)
    T = np.zeros((7, 7), dtype=np.int64)
    T[0, 0], T[1, 1], T[2, 2], T[3, 3] = a, b, c, 1
    T[4, 4], T[5, 5], T[6, 6] = INV[a], INV[b], INV[c]
    return T
def frob_perm():
    f3 = np.array([G.fmul(G.fmul(x, x), x) for x in range(q)])
    Cc = f3[G.C]                       # apply x -> x^3 coordinatewise
    return G.ids_of(Cc)
out = {}
# a generator of GF(9)^*: find element of order 8
for w in range(1, 9):
    o = 1; x = w
    while x != 1: x = G.fmul(x, w); o += 1
    if o == 8: gen = w; break
print('GF9* generator', gen)
for a, b in [(gen, 1), (1, gen), (gen, gen), (gen, G.fmul(gen, gen))]:
    T = torus(a, b)
    out['T_%d_%d' % (a, b)] = G.perm(T)
out['FROB'] = frob_perm()
for k, p in out.items():
    print(k, 'perm ok', len(set(p.tolist())) == N, 'fixes', int((p == np.arange(N)).sum()))
# verify lines preserved
lineset = set(tuple(sorted(r)) for r in G.LP.tolist())
for k, p in out.items():
    ok = all(tuple(sorted(p[r].tolist())) in lineset for r in G.LP.tolist()[:3000])
    print(k, 'lines ok (sample)', ok)
pickle.dump(out, open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/extra9.pkl', 'wb'))

# Independent builder: Haar graph of a metacyclic group, or a voltage lift over Z_p^2 x|_M Z_m. Writes "n" then edges "u v".
import sys
def meta(a_mod, m, r, gens, out):
    assert pow(r, m, a_mod) == 1
    idx = lambda a, j: j * a_mod + a
    N = a_mod * m
    mul = lambda g, h: ((g[0] + pow(r, g[1], a_mod) * h[0]) % a_mod, (g[1] + h[1]) % m)
    E = []
    for j in range(m):
        for a in range(a_mod):
            for s in gens:
                sg = mul(s, (a, j))
                E.append((idx(a, j), N + idx(*sg)))   # (g,A) ~ (s g, B)
    write(2 * N, E, out)
def lift(p, M, m, base_edges, nb, out):
    def mv(Mj, v): return ((Mj[0]*v[0] + Mj[1]*v[1]) % p, (Mj[2]*v[0] + Mj[3]*v[1]) % p)
    def mm(A, B): return ((A[0]*B[0]+A[1]*B[2]) % p, (A[0]*B[1]+A[1]*B[3]) % p, (A[2]*B[0]+A[3]*B[2]) % p, (A[2]*B[1]+A[3]*B[3]) % p)
    P = [(1, 0, 0, 1)]
    for _ in range(m): P.append(mm(P[-1], M))
    assert P[m] == (1, 0, 0, 1)
    G = [(x, y, j) for x in range(p) for y in range(p) for j in range(m)]
    gi = {g: i for i, g in enumerate(G)}
    mul = lambda g, h: ((lambda v: (v[0], v[1]))(tuple((a + b) % p for a, b in zip(g[:2], mv(P[g[2]], h[:2]))))) + ((g[2] + h[2]) % m,)
    n = len(G)
    E = [(u * n + gi[g], w * n + gi[mul(g, al)]) for (u, w, al) in base_edges for g in G]
    write(nb * n, E, out)
def write(n, E, out):
    with open(out, 'w') as f:
        f.write(f'{n}\n'); f.writelines(f'{u} {v}\n' for u, v in E)
    print(out, n, len(E))
if sys.argv[1] == 'meta':
    a_mod, m, r = map(int, sys.argv[2:5]); gens = [tuple(map(int, x.split(','))) for x in sys.argv[5:-1]]
    meta(a_mod, m, r, gens, sys.argv[-1])
else:
    p = int(sys.argv[2]); M = tuple(map(int, sys.argv[3].split(','))); m = int(sys.argv[4])
    be = []
    for x in sys.argv[5:-1]:
        u, w, al = x.split(':'); be.append((int(u), int(w), tuple(map(int, al.split(',')))))
    lift(p, M, m, be, 4, sys.argv[-1])

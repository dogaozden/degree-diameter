"""(12,5) chart lift 8748 minus one perfect matching: drop the edges of colour c with lambda in DROP[c-edge].
usage: python3 del8748.py mode out.edges   mode: 'c<colour>l<lam>' (same lambda on every base edge of that colour)
       or 'rand<seed>' (random colour per base vertex pair... see code)"""
import sys, itertools, random
sys.path.insert(0, "/home/user/degree-diameter/research/theorems/chartlift/graphs")
import build_d12D5_n8748 as B
mode, out = sys.argv[1], sys.argv[2]
q, Q, G, R = B.q, B.Q, B.G, B.R
m = R * G; nA = m * Q; E = []
vecs = list(itertools.product(range(q), repeat=4))
if mode.startswith("c"):
    c0 = int(mode[1]); l0 = int(mode[3])
    drop = lambda bi, c, x, u, lam: c == c0 and lam == l0
elif mode.startswith("rand"):
    rng = random.Random(int(mode[4:]))
    # pick, per controller edge (base edge, x) of colour c0, a random perfect matching of the K_{3,3} blocks: lam = pi(u) depends on u
    c0 = 0
    tab = {}
    def drop(bi, c, x, u, lam):
        if c != c0: return False
        key = (bi, x, tuple(u))
        if key not in tab: tab[key] = rng.randrange(3)
        return lam == tab[key]
for bi, (i, j, c, v) in enumerate(B.BASE):
    for x in range(G):
        a, bb = i * G + x, j * G + B.gmul(v, x)
        for u in vecs:
            y0 = B.mat_vec(B.A[c], u)
            for lam in range(q):
                if drop(bi, c, x, u, lam): continue
                y = [B.ADD[p][B.MUL[lam][t]] for p, t in zip(y0, B.B[c])]
                E.append((a * Q + B.vid(u), nA + bb * Q + B.vid(y)))
with open(out, "w") as f:
    f.write(f"{2*nA}\n"); f.writelines(f"{a} {b}\n" for a, b in E)
print(mode, "vertices", 2 * nA, "edges", len(E))

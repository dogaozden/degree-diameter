"""Twisted Omega H_q (reading 2): copy c is relabelled by a random class-preserving permutation pi_c of B_1, i.e. the new
vertex (t,k) is joined to pi_c(t) in copy c instead of t. Same degrees and order as Omega H_q; tests whether far pairs can
be repaired by relabelling.  usage: twist.py HEX TYPES SEED OUT"""
import sys, numpy as np
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split())
L = np.array([list(map(int, f.readline().split())) for _ in range(nl)], dtype=np.int64)
types, seed, out = sys.argv[2], int(sys.argv[3]), sys.argv[4]
rng = np.random.default_rng(seed); N1 = 2 * n; al = len(types); C = 5 * al; base = C * N1; nv = base + 10 * n
E = []
pts = L.ravel(); lns = np.repeat(np.arange(nl), q + 1) + n
for c in range(C): E.append(np.stack([c * N1 + pts, c * N1 + lns], 1))
pi = [np.concatenate([rng.permutation(n), n + rng.permutation(n)]) if seed >= 0 else np.arange(N1) for c in range(C)]
t = np.arange(n)
for B, ty in enumerate(types):
    for k in range(5):
        for bar in range(2):
            if ty == 'a': cs = [k + 4, k + 1] if not bar else [k + 2, k + 3]
            else: cs = [k + 3, k + 4] if not bar else [k + 4, k + 1]
            v = t if not bar else n + t
            h = base + 10 * t + 5 * bar + k
            for c in cs:
                cc = 5 * B + c % 5; E.append(np.stack([h, cc * N1 + pi[cc][v]], 1))
E = np.concatenate(E)
with open(out, 'w') as o:
    o.write(f"{nv}\n"); np.savetxt(o, E, fmt="%d")
print(nv, len(E))

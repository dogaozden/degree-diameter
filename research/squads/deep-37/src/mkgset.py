"""Write a group file for G = <z, s> on a Z_M-lift vertex set (like r2f/mkgroup.py, no start graph), optionally with
a colour-reversing s. usage: mkgset.py M K ALPHA SIGA SIGB OUT [rev]
 colour-preserving: s(u,h) = (sigma u, alpha h), sigma = SIGA on A (u < K), SIGB on B (cycle-type lists).
 rev: s maps A -> B: s(a_i, h) = (b_{pi(i)}, alpha h), s(b_i, h) = (a_{rho(i)}, alpha h) with SIGA giving the cycle type of
 s^2 on A ... (simple version: SIGA lists cycle lengths of the permutation tau of 0..2K-1 that swaps sides)."""
import sys
M, K, alpha = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) % int(sys.argv[1])
def cyc(s):
    lens = [int(x) for x in s.split(',') if x]; perm = []; pos = 0; p = list(range(sum(lens)))
    for L in lens:
        c = list(range(pos, pos + L)); pos += L
        for i, x in enumerate(c): p[x] = c[(i+1) % L]
    return p
if sys.argv[4].startswith('perm:'):
    sig = [int(x) for x in sys.argv[4][5:].split(',')]; assert sorted(sig) == list(range(2*K))
else:
    pA, pB = cyc(sys.argv[4]), cyc(sys.argv[5]); assert len(pA) == K and len(pB) == K
    sig = pA + [K + x for x in pB]
n = 2*K*M
vid = lambda u, h: u*M + (h % M)
gens = [[vid(v//M, v % M + 1) for v in range(n)], [vid(sig[v//M], alpha*(v % M)) for v in range(n)]]
I = tuple(range(n)); G = {I}; fr = [I]
while fr:
    nf = []
    for p in fr:
        for g in gens:
            q = tuple(g[p[x]] for x in range(n))
            if q not in G: G.add(q); nf.append(q)
    fr = nf
G = sorted(G)
with open(sys.argv[6], 'w') as f:
    f.write(f"{n} {len(G)}\n")
    for p in G: f.write(" ".join(map(str, p)) + "\n")
    f.write(" ".join('0' if v//M < K else '1' for v in range(n)) + "\n")
print("order", len(G), "n", n)

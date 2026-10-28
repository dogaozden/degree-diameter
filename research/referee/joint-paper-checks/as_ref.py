"""Referee check of Section 4.2: AS(q) in the coordinates printed, Theorem 4.7 and Corollary 4.8 (graph written
for the C checker), plus the remark that AS(3) has no 1-ovoid (exhaustive)."""
import sys, itertools
from gf import GF
def AS(q):
    F = GF(q); E = list(F.elts()); M, A_, S_ = F.mul, F.add, F.sub
    pts = [(a, b, c) for a in E for b in E for c in E]          # (a:1:b:c)
    lines = set()
    for (b0, c0) in itertools.product(E, E):
        lines.add(frozenset((a, b0, c0) for a in E))            # fibres
    dirs = [(1, d2) for d2 in E] + [(0, 1)]
    for (a0, b0, c0) in pts:
        for (d1, d2) in dirs:
            rho = S_[M[b0][d2]][M[c0][d1]]
            lines.add(frozenset((A_[a0][M[l][rho]], A_[b0][M[l][d1]], A_[c0][M[l][d2]]) for l in E))
    lines = sorted(lines, key=sorted)
    return F, pts, lines
def check(q):
    F, pts, lines = AS(q); E = list(F.elts()); M = F.mul
    assert len(lines) == q*q*(q+2) and all(len(L) == q for L in lines)
    on = {p: [i for i, L in enumerate(lines) if p in L] for p in pts}
    assert all(len(v) == q + 2 for v in on.values())
    # GQ axiom on a sample: for an anti-flag exactly one point of L collinear with p
    coll = {p: set().union(*[lines[i] for i in on[p]]) - {p} for p in pts}
    for p in pts[:40]:
        for L in lines:
            if p not in L: assert len(L & coll[p]) == 1
    eps = next(x for x in E if x and F.chi(x) == -1)
    n = lambda b, c: F.sub[M[b][b]][M[eps][M[c][c]]]
    k1 = F.inv[2 % F.p if F.p > 2 else 1] if True else None
    k1 = F.inv[F.from_int(2)]; k2 = F.inv[M[F.from_int(2)][eps]]
    assert M[k1][k2] == F.inv[M[F.from_int(4)][eps]]
    E1 = {(M[k1][n(b, c)], b, c) for b in E for c in E}; E2 = {(M[k2][n(b, c)], b, c) for b in E for c in E}
    assert E1 & E2 == {(0, 0, 0)}
    sums = set(len(L & E1) + len(L & E2) for L in lines)
    # all products kappa1*kappa2 = 1/(4 eps): every such pair
    allok = True
    for ka in range(1, q):
        kb = M[F.inv[ka]][F.inv[M[F.from_int(4)][eps]]]
        A1 = {(M[ka][n(b, c)], b, c) for b in E for c in E}; A2 = {(M[kb][n(b, c)], b, c) for b in E for c in E}
        allok &= all(len(L & A1) + len(L & A2) == 2 for L in lines)
    print(f"q={q}: AS(q) {len(pts)} points, {len(lines)} lines, GQ sample ok; line sums with kappa=(1/2,1/(2eps)): {sums}; all kappa1*kappa2=1/(4eps): {allok}")
    # Corollary 4.8 graph
    idx = {p: i for i, p in enumerate(pts)}; nP = len(pts); nL = len(lines)
    clones = [p for p in pts if p in E1] + [p for p in pts if p in E2]
    edges = []
    for i, L in enumerate(lines):
        for p in L: edges.append((idx[p], nP + i))
    for j, p in enumerate(clones):
        for i in on[p]: edges.append((nP + nL + j, nP + i))
    N = nP + nL + len(clones)
    with open(f"as_cor48_q{q}.edges", "w") as f:
        f.write(f"{N} {len(edges)}\n" + "\n".join(f"{u} {v}" for u, v in edges) + "\n")
    print(f"   Cor 4.8 graph: {N} vertices (2q^2(q+2)={2*q*q*(q+2)}), written as_cor48_q{q}.edges")
    return pts, lines, on
def no_one_ovoid(q):
    F, pts, lines = AS(q)
    on = {p: [i for i, L in enumerate(lines) if p in L] for p in pts}
    covered = [0] * len(lines); sol = []
    def rec():
        try: i = covered.index(0)
        except ValueError: return True
        for p in lines[i]:
            if all(covered[j] == 0 for j in on[p]):
                for j in on[p]: covered[j] = 1
                sol.append(p)
                if rec(): return True
                sol.pop()
                for j in on[p]: covered[j] = 0
        return False
    return rec()
if __name__ == '__main__':
    for q in [3, 5, 7, 9]:
        check(q)
    print("AS(3) has a 1-ovoid:", no_one_ovoid(3), "(so no 2-ovoid either: complement of a 2-ovoid in 3-point lines is a 1-ovoid)")

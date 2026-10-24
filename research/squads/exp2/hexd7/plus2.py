"""Beat 3·|H(q)| by 2: the 3-copy graph with one point p "unhooked" in all three copies, plus a 2-vertex gadget.

Base: Z3 copies of the incidence graph of H(q), cross edges (y, c) ~ (phi(y), c+1) for every point y (phi any bijection
points -> lines; threecopy.py). Change: delete the three cross edges of p, i.e. (p, c) ~ (phi(p), c+1), and add
x ~ (p, 0), (p, 1), (p, 2), w;  w ~ (L0, 0), (L0, 1), (L0, 2), x  with L0 = phi(p). Max degree stays q+2, n = 6P + 2.

Every pair not involving the deleted edges keeps the routes of the 3-copy proof. Working through the cases for
a = (p, c) and b = (L0, c+1), the graph has diameter 7 iff
  (A) every point opposite p lies on a line phi(y) with y in B4(p) - {p}  (B4 = within distance 4 in Gamma), and
  (B) every line opposite L0 passes through a point phi^-1(M) with M in B4(L0) - {L0}.
phi is built to satisfy both: greedy covers C_A (lines at distance 5 from p, 6 from L0) and C_B (points at distance 5
from L0, 6 from p), each of size <= |B4| - 1, placed on disjoint domains, the rest of phi arbitrary.

usage: python3 plus2.py q OUT.edges [seed [PHI]]   (PHI: a bijection from plus2ls.c to use instead of the greedy one)
"""
import sys, random
from hexagon import build


def bfs_inc(P, pl, lp, src):
    """distances in the incidence graph; vertices 0..P-1 points, P..2P-1 lines"""
    n = 2 * P
    adj = lambda v: [P + l for l in lp[v]] if v < P else list(pl[v - P])
    d = [-1] * n
    d[src] = 0
    fr = [src]
    while fr:
        nx = []
        for u in fr:
            for w in adj(u):
                if d[w] < 0:
                    d[w] = d[u] + 1
                    nx.append(w)
        fr = nx
    return d


def greedy_cover(targets, cands, members, rng):
    """pick candidates until every target is covered; members(c) -> iterable of targets covered by c"""
    unc = set(targets)
    cover = []
    cnt = {c: len(unc & set(members(c))) for c in cands}
    while unc:
        best = max(cnt.values())
        pick = rng.choice([c for c, v in cnt.items() if v == best])
        cover.append(pick)
        newly = unc & set(members(pick))
        unc -= newly
        del cnt[pick]
        for c in cnt:
            if cnt[c]:
                cnt[c] -= len(newly & set(members(c)))
    return cover


def main():
    q, out = int(sys.argv[1]), sys.argv[2]
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    P, pl, lp = build(q, check=False)
    p = 0
    L0 = lp[p][0]                       # phi(p): a line through p
    dp = bfs_inc(P, pl, lp, p)          # dp[v], v < P point, v >= P line
    dL = bfs_inc(P, pl, lp, P + L0)
    B4p = [y for y in range(P) if dp[y] <= 4 and y != p]
    B4L = [M for M in range(P) if dL[P + M] <= 4 and M != L0]
    assert len(B4p) == len(B4L) == (q ** 5 - 1) // (q - 1) - 1
    opp_pts = [z for z in range(P) if dp[z] == 6]
    opp_lines = [M for M in range(P) if dL[P + M] == 6]
    candA = [M for M in range(P) if dp[P + M] == 5 and dL[P + M] == 6]
    candB = [y for y in range(P) if dL[y] == 5 and dp[y] == 6]
    import os
    if os.environ.get('NOGREEDY'):   # large q: start from a random phi (with phi(p) = L0); plus2ls.c does the rest
        CA, CB = [], []
    else:
        CA = greedy_cover(opp_pts, candA, lambda M: pl[M], rng)
        CB = greedy_cover(opp_lines, candB, lambda y: lp[y], rng)
    print('q=%d P=%d |B4|-1=%d opposite points %d lines %d; cover sizes |C_A|=%d |C_B|=%d (need <= %d)'
          % (q, P, len(B4p), len(opp_pts), len(opp_lines), len(CA), len(CB), len(B4p)), flush=True)
    if len(CA) > len(B4p) or len(CB) > len(B4L):
        print('covers too large for the strict (A)/(B); truncating, the local search (plus2ls.c) fixes the rest')
        CA, CB = CA[:len(B4p)], CB[:len(B4L)]
    phi = [-1] * P
    phi[p] = L0
    # (A): B4(p)-{p} -> C_A + filler lines (not L0, not in B4(L0), not in C_A)
    usedL = set(CA) | {L0}
    B4Lset = set(B4L)
    fillA = [M for M in range(P) if M not in usedL and M not in B4Lset]
    rng.shuffle(fillA)
    imgA = list(CA) + fillA[:len(B4p) - len(CA)]
    ys = list(B4p)
    rng.shuffle(ys)
    for y, M in zip(ys, imgA):
        phi[y] = M
    usedL |= set(imgA)
    # (B): C_B + filler points (not p, not in B4(p), not in C_B) -> B4(L0)-{L0}
    B4pset = set(B4p) | {p}
    CBset = set(CB)
    fillB = [y for y in range(P) if y not in B4pset and y not in CBset]
    rng.shuffle(fillB)
    preB = list(CB) + fillB[:len(B4L) - len(CB)]
    Ms = list(B4L)
    rng.shuffle(Ms)
    for y, M in zip(preB, Ms):
        assert phi[y] < 0
        phi[y] = M
    usedL |= set(B4L)
    restP = [y for y in range(P) if phi[y] < 0]
    restL = [M for M in range(P) if M not in usedL]
    assert len(restP) == len(restL)
    rng.shuffle(restL)
    for y, M in zip(restP, restL):
        phi[y] = M
    assert sorted(phi) == list(range(P))
    # export for the local search, and optionally read an improved phi back
    with open(out + '.hfile', 'w') as f:
        f.write('%d %d\n' % (P, q))
        f.write(''.join(' '.join(map(str, ln)) + '\n' for ln in pl))
    with open(out + '.phi0', 'w') as f:
        f.write(' '.join(map(str, phi)) + '\n')
    print('p=%d L0=%d; wrote %s.hfile and %s.phi0' % (p, L0, out, out))
    if len(sys.argv) > 4:
        phi = list(map(int, open(sys.argv[4]).read().split()))
        assert sorted(phi) == list(range(P)) and phi[p] == L0
        print('using phi from', sys.argv[4])
    # graph
    blk = 2 * P
    E = []
    for c in range(3):
        base = c * blk
        for l, ln in enumerate(pl):
            for y in ln:
                E.append((base + y, base + P + l))
        nb = ((c + 1) % 3) * blk
        for y in range(P):
            if y != p:
                E.append((base + y, nb + P + phi[y]))
    x, w = 3 * blk, 3 * blk + 1
    for c in range(3):
        E.append((c * blk + p, x))
        E.append((c * blk + P + L0, w))
    E.append((x, w))
    n = 3 * blk + 2
    with open(out, 'w') as f:
        f.write('%d\n' % n)
        f.write(''.join('%d %d\n' % e for e in E))
    print('wrote %s: n=%d edges=%d (3 copies of H(%d) + 2, max degree %d)' % (out, n, len(E), q, q + 2))
    with open(out + '.phi', 'w') as f:
        f.write(' '.join(map(str, phi)) + '\n')


if __name__ == '__main__':
    main()

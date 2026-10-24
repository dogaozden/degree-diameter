#!/usr/bin/env python3
"""Build hub-graph designs (format of research/d15D7/pg27.hg) for K = 9..56 and verify each with checker.py.

Construction A (cyclic): find D in Z_K, |D| = s <= 8, with D - D = Z_K \\ {0}. Edges: a ~ (a + d) mod K, a in Z_K, d in D.
  Line-side hubs a, a' share the point-side neighbour b = a + d = a' + d' iff a - a' = d' - d lies in D - D, so the
  covering gives (ii). Point-side hubs b, b' share a = b - d = b' - d' iff b - b' lies in D - D, which gives (iii).
  Every hub has degree s <= 8. Covering needs K - 1 <= s(s - 1), so this route stops at K = 57 for s = 8.
  (For K = 56 it is impossible with s = 8: 28 unordered pairs must hit 28 classes {+-t} exactly once, and the number
  of pairs with odd difference e(8-e) is never 14.)

Construction B (groups): a group G of order K and D in G with 1 in D, |D| <= 8, such that D D^-1 and D^-1 D both
  contain G \\ {1}. Edges: g ~ h iff g^-1 h in D, i.e. h = g d. Then N(g) = gD and N(h) = h D^-1, and
  gD meets g'D iff g'^-1 g in D D^-1; hD^-1 meets h'D^-1 iff h'^-1 h in D^-1 D. Used for K = 56 (Z_56 is excluded there),
  with the semidirect products Z_7 x| P, P in {Z_8, Q_8}, which have a unique involution.

Status (checked by checker.py):
  K = 9..51: PASS (cyclic, |D| <= 8). Files hgK.hg in this folder.
  K = 52, 53, 54, 55: no design found. cyc_exh.c (exhaustive, WLOG 0,1 in D) finds no cyclic D of size 8 for
  n = 52..55; group_designs.py (group_exh.c, exhaustive) finds none in any metacyclic group of order 52, 54 or 55
  (order 53 is prime, so only Z_53 exists). Non-Cayley structures are not searched.
  K = 56: impossible. Every hub then has degree exactly 8 (7*deg >= 55 forces deg 8), so M M^T = J + 7I + P with
  P the permutation matrix of a perfect matching (each pair of line-side hubs has 1 common neighbour, except one
  partner with 2). Eigenvalues 64, 8 (x27), 6 (x28) give det(M)^2 = 64 * 8^27 * 6^28, whose 2-adic valuation 115
  is odd, so no integer M exists. (Groups of order 56 fail for the same reason, by a parity count.)
  K = 57: PG(2,7) (pg27.hg; also Z_57 with the Singer set {0,1,3,13,32,36,43,52}).
  K >= 58: impossible. Line-side hub a has <= 8 neighbours, each with <= 7 other line-side hubs, so at most 56 hubs
  can share a neighbour with a, hence K - 1 <= 56.

Usage: python3 make_designs.py            (writes hgK.hg for each K it can, and prints a summary)
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from checker import check_file  # noqa: E402

MAXDEG = 8
KMIN, KMAX = 9, 56


# ---------------------------------------------------------------- construction A: cyclic difference covers
def cyc_uncovered(K, D):
    cov = set()
    for x in D:
        for y in D:
            if x != y:
                cov.add((x - y) % K)
    return (K - 1) - len(cov)


def search_cyclic(K, s, rng, restarts=60, steps=6000):
    """Hill-climb (with sideways moves and occasional random kicks) for D of size s containing 0."""
    for _ in range(restarts):
        D = [0] + rng.sample(range(1, K), s - 1)
        cur = cyc_uncovered(K, D)
        for _ in range(steps):
            if cur == 0:
                return sorted(D)
            i = rng.randrange(1, s)
            new = rng.randrange(1, K)
            if new in D:
                continue
            D2 = D[:]
            D2[i] = new
            c2 = cyc_uncovered(K, D2)
            if c2 <= cur or rng.random() < 0.03:
                D, cur = D2, c2
        if cur == 0:
            return sorted(D)
    return None


def cyclic_edges(K, D):
    return [(a, (a + d) % K) for a in range(K) for d in D]


# ---------------------------------------------------------------- construction B: groups
class Group:
    """Finite group on 0..n-1 with multiplication table mul[g][h], inverses inv[g], identity e."""

    def __init__(self, name, mul, inv, e):
        self.name, self.mul, self.inv, self.e = name, mul, inv, e
        self.n = len(mul)


def semidirect_Z7(name, Pm, Pinv, Pid, chi):
    """Z_7 x| P where p acts on Z_7 by x -> chi[p] * x (chi: P -> {+1,-1} a homomorphism)."""
    np_ = len(Pm)
    n = 7 * np_

    def enc(x, p):
        return (x % 7) * np_ + p

    mul = [[0] * n for _ in range(n)]
    for g in range(n):
        x, p = divmod(g, np_)
        for h in range(n):
            y, q = divmod(h, np_)
            mul[g][h] = enc(x + chi[p] * y, Pm[p][q])
    inv = [0] * n
    for g in range(n):
        x, p = divmod(g, np_)
        inv[g] = enc(-chi[p] * x, Pinv[p])
    return Group(name, mul, inv, enc(0, Pid))


def cyclic_group(n):
    mul = [[(g + h) % n for h in range(n)] for g in range(n)]
    inv = [(-g) % n for g in range(n)]
    return Group(f"Z_{n}", mul, inv, 0)


def quaternion_group():
    """Q_8 as pairs (sign, unit), unit in '1','i','j','k'. Returns (Pm, Pinv, Pid, elems)."""
    units = ["1", "i", "j", "k"]
    table = {("1", "1"): (1, "1"), ("1", "i"): (1, "i"), ("1", "j"): (1, "j"), ("1", "k"): (1, "k"),
             ("i", "1"): (1, "i"), ("j", "1"): (1, "j"), ("k", "1"): (1, "k"),
             ("i", "i"): (-1, "1"), ("j", "j"): (-1, "1"), ("k", "k"): (-1, "1"),
             ("i", "j"): (1, "k"), ("j", "i"): (-1, "k"), ("j", "k"): (1, "i"), ("k", "j"): (-1, "i"),
             ("k", "i"): (1, "j"), ("i", "k"): (-1, "j")}
    elems = [(s, u) for s in (1, -1) for u in units]
    idx = {e: i for i, e in enumerate(elems)}
    Pm = [[0] * 8 for _ in range(8)]
    for a, (sa, ua) in enumerate(elems):
        for b, (sb, ub) in enumerate(elems):
            s, u = table[(ua, ub)]
            Pm[a][b] = idx[(sa * sb * s, u)]
    Pid = idx[(1, "1")]
    Pinv = [next(b for b in range(8) if Pm[a][b] == Pid) for a in range(8)]
    return Pm, Pinv, Pid, elems


def groups_of_order_56():
    """Groups with a unique involution (all others are excluded by the counting argument), plus Z_56 for reference."""
    out = []
    z8 = cyclic_group(8)
    Pm8 = z8.mul
    Pinv8 = z8.inv
    out.append(semidirect_Z7("Z7:Z8 (kernel Z4)", Pm8, Pinv8, 0, [(-1) ** p for p in range(8)]))
    out.append(semidirect_Z7("Z7:Z8 trivial = Z56", Pm8, Pinv8, 0, [1] * 8))
    Pm, Pinv, Pid, elems = quaternion_group()
    # chi with kernel <i>: +1 on {1, -1, i, -i}, -1 on {j, -j, k, -k}
    chi_i = [(-1 if u in ("j", "k") else 1) for (_, u) in elems]
    out.append(semidirect_Z7("Z7:Q8 (kernel <i>)", Pm, Pinv, Pid, chi_i))
    out.append(semidirect_Z7("Z7 x Q8", Pm, Pinv, Pid, [1] * 8))
    return out


def group_cover_cost(G, D):
    mul, inv, e = G.mul, G.inv, G.e
    s1, s2 = set(), set()
    for d in D:
        for f in D:
            if d != f:
                s1.add(mul[d][inv[f]])
                s2.add(mul[inv[d]][f])
    return (G.n - 1 - len(s1)) + (G.n - 1 - len(s2))


def search_group(G, s, rng, restarts=40, steps=6000):
    e = G.e
    others = [g for g in range(G.n) if g != e]
    for _ in range(restarts):
        D = [e] + rng.sample(others, s - 1)
        cur = group_cover_cost(G, D)
        for _ in range(steps):
            if cur == 0:
                return D
            i = rng.randrange(1, s)
            new = rng.choice(others)
            if new in D:
                continue
            D2 = D[:]
            D2[i] = new
            c2 = group_cover_cost(G, D2)
            if c2 <= cur or rng.random() < 0.03:
                D, cur = D2, c2
        if cur == 0:
            return D
    return None


def group_edges(G, D):
    return [(g, G.mul[g][d]) for g in range(G.n) for d in D]


# ---------------------------------------------------------------- output
def write_hg(path, K, edges):
    with open(path, "w") as f:
        f.write(f"{K} {len(edges)}\n")
        for j, k in edges:
            f.write(f"{j} {k}\n")


def build(K):
    """Return (method, edges) for K, or (None, None). Tries cyclic first, then groups."""
    rng = random.Random(1000 + K)
    for s in range(3, MAXDEG + 1):
        D = search_cyclic(K, s, rng)
        if D is not None:
            return f"cyclic Z_{K}, D={D}", cyclic_edges(K, D)
    if K == 56:
        for G in groups_of_order_56():
            for s in range(6, MAXDEG + 1):
                D = search_group(G, s, rng)
                if D is not None:
                    return f"group {G.name}, D={D}", group_edges(G, D)
    return None, None


def main():
    results = {}
    for K in range(KMIN, KMAX + 1):
        method, edges = build(K)
        path = os.path.join(HERE, f"hg{K}.hg")
        if edges is None:
            results[K] = (False, "no construction found")
            print(f"K={K:2d}: no design found")
            continue
        write_hg(path, K, edges)
        ok, info = check_file(path)
        results[K] = (ok, method)
        print(f"K={K:2d}: {'PASS' if ok else 'FAIL'}  {method}  m={info['m']} maxdeg={info['maxdeg']}")
    passed = [K for K, (ok, _) in results.items() if ok]
    print(f"\nscore: {len(passed)} of {KMAX - KMIN + 1} values of K in [{KMIN},{KMAX}] pass the checker")
    print("passing K:", passed)
    print("failing K:", [K for K in results if K not in passed])
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""List all (alpha, beta) degree-sequence cubes for k = 11 (B = arcs from O to I at vertex 0, 9 x 9).
Every pair of non-increasing sequences that a solution can have is listed; the pruning rules are proved in
NOTES.md / PROOF.md:
  - entries in {0,...,6, 9}: a row (column) sum of 7 or 8 would leave a 2-regular graph on 1 or 2 vertices
    (2-factor lemma, NOTES item 4 / 9);
  - at most one entry 9, and if some entry is 9 every other entry is 2 (a column z with 9 in-neighbours in O has
    S_z empty, so CI(z,z') = |N^-(z) cap N^-(z')| = beta_z' must be 2; same for rows);
  - sum_x C(alpha_x,2) <= 72 - (lower bound for sum_y C(a_y,2)), using sum_y a_y = 81 - t and the vertex sums
    2(9 - alpha_x) of the edge weighting a on the pairs of O (NOTES item 10); same for beta;
  - (alpha, beta) satisfies Gale-Ryser (a 0/1 matrix with these margins exists);
  - alpha >= beta lexicographically: reversing all arcs maps a solution to a solution (Theorem Q is symmetric under
    transposition) and swaps O and I at vertex 0, so B becomes B^T and the cube (alpha, beta) becomes (beta, alpha).
usage: ablist.py out.txt [--maxtau]     (one cube per line: a1,..,a9/b1,..,b9)
--maxtau: rule 'arc 0->1 lies on the most directed triangles' instead of the reversal halving: keep beta_1 <= alpha_1
          (beta_j counts the triangles on the arc z_j -> 0) and no alpha >= beta restriction."""
import sys
vals = [9, 6, 5, 4, 3, 2, 1, 0]
def parts(t, n=9):
    out = []
    def rec(pre, rem, mx):
        if len(pre) == n:
            if rem == 0: out.append(tuple(pre))
            return
        for v in vals:
            if v > mx or v > rem: continue
            if v * (n - len(pre)) < rem: break
            rec(pre + [v], rem - v, v)
    rec([], t, 9); return out
def C2(x): return x * (x - 1) // 2
def minC_k(s, k):
    q, r = divmod(s, k); return r * C2(q + 1) + (k - r) * C2(q)
def ok(a):
    if a.count(9) > 1: return False
    if 9 in a and any(x != 2 for x in a if x != 9): return False
    Q = 72 - sum(C2(x) for x in a)
    return Q >= 0 and sum(minC_k(2 * (9 - x), 8) for x in a) / 2 <= Q
def gale_ryser(a, b):
    return sum(a) == sum(b) and all(sum(a[:k]) <= sum(min(bj, k) for bj in b) for k in range(1, len(a) + 1))
with open(sys.argv[1], 'w') as f:
    n = 0
    for t in range(0, 82):
        P = [a for a in parts(t) if ok(a)]
        for a in P:
            for b in P:
                keep = (b[0] <= a[0]) if '--maxtau' in sys.argv else (a >= b)
                if keep and gale_ryser(a, b):
                    f.write(','.join(map(str, a)) + '/' + ','.join(map(str, b)) + '\n'); n += 1
print(n, 'cubes')

"""Card v3: check the lemma |(S-S)+(S-S)| <= N(d) for abelian groups, |S| = d.

Proof as checked (d = |S|):
  Write a-b+c-d = sigma(P) - sigma(Q), P = {a,c}, Q = {b,d} (2-multisets of S).
  (i) P and Q share an element: the value reduces to x - y, x,y in S, so it lies in S-S
      (at most d(d-1)+1 values, including 0).
  (ii) P and Q have disjoint supports: the value is determined by the ordered pair (P,Q).
       Count: P = {a,a} (d ways), Q a 2-multiset on the other d-1 elements (C(d,2) ways);
              P = {a,b}, a!=b (C(d,2) ways), Q a 2-multiset on the other d-2 (C(d-1,2) ways).
       Total disjoint pairs = d*C(d,2) + C(d,2)*C(d-1,2).
  So N(d) = 1 + d(d-1) + d*C(d,2) + C(d,2)*C(d-1,2);  N(6) = 1 + 30 + 90 + 150 = 271.
Sharpness: in Z^d with S the standard basis, all N(d) values are distinct, so N(d) is attained
in the infinite abelian group Z^d. This script checks the counts by brute force and the
free-group count for d = 2..6.
"""
from itertools import combinations_with_replacement, product
from math import comb


def N_formula(d):
    return 1 + d * (d - 1) + d * comb(d, 2) + comb(d, 2) * comb(d - 1, 2)


def count_disjoint_pairs(d):
    ms = list(combinations_with_replacement(range(d), 2))  # all 2-multisets
    cnt = 0
    for P in ms:
        for Q in ms:
            if not set(P) & set(Q):
                cnt += 1
    return cnt


def free_count(d):
    """Distinct values of (S-S)+(S-S) in Z^d with S = standard basis (formal count)."""
    basis = [tuple(1 if i == j else 0 for i in range(d)) for j in range(d)]
    def sub(u, v):
        return tuple(x - y for x, y in zip(u, v))
    def add(u, v):
        return tuple(x + y for x, y in zip(u, v))
    SS = {sub(a, b) for a in basis for b in basis}
    T = {add(u, v) for u in SS for v in SS}
    return len(SS), len(T)


if __name__ == "__main__":
    for d in range(2, 7):
        ss, t = free_count(d)
        print(f"d={d}: N(d)={N_formula(d)}  |S-S| free={ss} (<= {d*(d-1)+1})  "
              f"|(S-S)+(S-S)| free={t}  disjoint pairs={count_disjoint_pairs(d)} "
              f"(formula {d*comb(d,2)+comb(d,2)*comb(d-1,2)})")

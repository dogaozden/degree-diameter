"""Reference (slow, exact) computation of the D-perfect cost of a chart over any F_q: for both start sides and every
reduced colour word y of length <= n = D-1 with |y| = n mod 2, the union of the spans of all words of length n
reducing to y must be F_q^n; cost = total number of uncovered vectors.  Cross-checks perfect2.c (q = 2).
usage: python3 tree_perfect.py CHART.txt q k D   (chart in the bit/entry format: k lines of n*n entries, k lines b_c)"""
import sys, itertools
from chartlib import Chart
from gf import GF

def load(path, q, k, n):
    vals = [list(map(int, l.split())) for l in open(path) if l.strip()]
    A = [tuple(tuple(r[t * n:(t + 1) * n]) for t in range(n)) for r in vals[:k]]
    b = [tuple(r) for r in vals[k:2 * k]]
    return Chart(GF(q), A, b)

def reduce(word):
    st = []
    for c in word:
        if st and st[-1] == c: st.pop()
        else: st.append(c)
    return tuple(st)

def cost(ch, D):
    n = D - 1; F = ch.F; total = 0
    for side in 'AB':
        cov = {}
        for word in itertools.product(range(ch.k), repeat=n):
            y = reduce(word)
            M, S = ch.walk(side, word)
            cov.setdefault(y, set()).update(F.span(S, n))
        for y, vs in cov.items():
            total += ch.q ** n - len(vs)
    return total

if __name__ == '__main__':
    path, q, k, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('reference cost', cost(load(path, q, k, D - 1), D))

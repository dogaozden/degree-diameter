#!/usr/bin/env python3
"""uncovered.py: list the uncovered elements of a (near-)solution of a Haar graph on prod G G x Z_n with the
swap-conjugation symmetry alpha(x1, x2, z) = (c x2 c^-1, x1, r z) of haar_order2 (ASWAPC=1), and describe them.
Usage: uncovered.py BEST.txt --conj "mat(a,b,c,d)" --r R"""
import argparse, re
import numpy as np
from hgroups import read_solution
from twist import Haar


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--conj", required=True)
    ap.add_argument("--r", type=int, required=True)
    A = ap.parse_args()
    d, D, G, S = read_solution(A.file)
    Q, n = G.Q, G.n
    g1, g2 = Q.g1, Q.g2
    c = g1.find(*map(int, re.match(r"mat\((\d+),(\d+),(\d+),(\d+)\)", A.conj).groups()))
    ci = int(g1.inv_vec(np.array([c]))[0])
    N = G.N
    allg = np.arange(N)
    xq, z = allg // n, allg % n
    x1, x2 = xq // g2.order, xq % g2.order
    y1 = g1.mul_vec(g1.mul_vec(np.full(N, c), x2), np.full(N, ci))
    alpha = (y1 * g2.order + x1) * n + (A.r * z) % n
    H = Haar(G, S)
    cost, lev, V = H.cost(D)
    print("cost", cost, "levels", lev)
    U = np.nonzero(~(V[1] if D % 2 == 0 else V[0][0]))[0]
    print("uncovered:", len(U))
    seen = set()
    for u in U:
        if int(u) in seen:
            continue
        orb = [int(u)]
        while True:
            w = int(alpha[orb[-1]])
            if w == orb[0]:
                break
            orb.append(w)
        seen.update(orb)
        print(f"  alpha-orbit of size {len(orb)}:")
        for w in orb:
            q, zz = w // n, w % n
            a1, a2 = q // g2.order, q % g2.order
            tr1, tr2 = int(g1.trace(np.array([a1]))[0]), int(g2.trace(np.array([a2]))[0])
            print(f"    {g1.desc(a1)} tr {tr1} ; {g2.desc(a2)} tr {tr2} ; z={zz}   in S: {w in S}")


if __name__ == "__main__":
    main()

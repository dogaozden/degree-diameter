#!/usr/bin/env python3
"""Orbit check for an S-frame hole set (from holes2.py logic): orbits of Gamma = <alpha, inverse> per kind.
usage: gamma.py EVALFILE p n [ORBFILE]   prints orbit sizes, alpha-fixed count, cost mod 3 test."""
import sys, math
sys.path.insert(0, '.')
import holes2 as H2
from collections import Counter

def main(fn, p, n, orb=None):
    H = H2.load_eval(fn)
    g = (0, p - 1, 1, p - 1); gi = H2.minv(g, p)
    best = None
    for r in range(2, max(n, 3)):
        if n > 1 and math.gcd(r, n) == 1 and pow(r, 3, n) == 1 % n:
            fx = math.gcd(r - 1, n)
            if best is None or fx < best[1]: best = (r, fx)
    AR = best[0] if (best and n > 1) else 1
    M0, z0 = H2.load_s0(orb) if orb else ((1, 0, 0, 1), 0)
    M0i = H2.minv(M0, p)
    items = []
    for M, z, k in H:
        if k == 'U' and M0 != (1, 0, 0, 1): M = H2.mmul(H2.mmul(M0i, M, p), M0, p)
        items.append((M, z % n if n > 1 else 0, k))
    alpha = lambda M, z: (H2.mmul(H2.mmul(g, M, p), gi, p), (AR * z) % n if n > 1 else 0)
    inv = lambda M, z: (H2.minv(M, p), (-z) % n if n > 1 else 0)
    print(f"# {fn}: p={p} n={n}, holes {len(items)}")
    total_fixed = 0; sizes = Counter(); blocks = []
    for kind in 'UT':
        S = {(M, z) for (M, z, k) in items if k == kind}
        seen = set()
        for x in sorted(S):
            if x in seen: continue
            orb = {x}; stack = [x]
            while stack:
                y = stack.pop()
                for w in (alpha(*y), inv(*y)):
                    if w not in orb: orb.add(w); stack.append(w)
            assert orb <= S, "Gamma-orbit leaves the hole set (symmetry claim fails)"
            seen |= orb
            afix = sum(1 for (M, z) in orb if alpha(M, z) == (M, z))
            sizes[(kind, len(orb))] += 1
            blocks.append((kind, len(orb), x, afix))
            if afix: total_fixed += afix
        print(f"# kind {kind}: {len(S)} holes; Gamma-orbits {[b[1] for b in blocks if b[0]==kind]}")
    print("# orbit size counts (kind,size):", dict(sizes))
    alpha_fixed_holes = sum(1 for (M, z, k) in items if alpha(M, z) == (M, z))
    print(f"# alpha-fixed holes: {alpha_fixed_holes}; cost {len(items)} mod 3 = {len(items) % 3}; test cost = #fixed mod 3: {len(items) % 3 == alpha_fixed_holes % 3}")
    for b in blocks:
        if b[1] <= 3 or b[3]:
            print("#  small/fixed block:", b[0], "size", b[1], "rep", b[2], "alpha-fixed in block", b[3])

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)

#!/usr/bin/env python3
"""Exact Haar search inside fixed coset patterns (hunt-d5): writes candidate lists for `haar5 prod`.

G = (Z_p x|_r Z_k) x Z_n, element (a, j, z) = index ((a*k + j)*n + z) (haar_fast / metatab.py numbering), G' = Z_p.
For a coset pattern J (multiset of d cosets (j, z) containing (0,0), see jpatterns.py) every S with that pattern is,
up to isomorphism of the Haar graph, one with
  * S[0] = e                                      (translation S -> S s^-1),
  * S[1] = (0, j1, z1) for the first coset with r^j1 != 1   (conjugation by (b,0,0) shifts a by (r^j - 1) b),
  * S[2] with a in {0, 1}                         (the automorphisms (a,j,z) -> (u a, j, z), u in Z_p^*, fix S[0], S[1]),
  * the other elements anywhere in their cosets.
So the product of these candidate lists covers every S with pattern J: `haar5 prod` over them is exact for cost 0.

Usage: jexact.py d p k r n PATTERNS OUT.lists   (PATTERNS: lines "mu j,z j,z ..." as printed by jpatterns.py)
"""
import sys

def main():
    d, p, k, r, n = map(int, sys.argv[1:6]); pats = sys.argv[6]; out = open(sys.argv[7], 'w')
    idx = lambda a, j, z: (a * k + j) * n + z
    nb = 0; total = 0
    for line in open(pats):
        if line.startswith('#') or not line.strip(): continue
        f = line.split(); mu = f[0]; cos = [tuple(map(int, t.split(','))) for t in f[1:]]
        assert len(cos) == d and (0, 0) in cos, line
        rest = sorted(cos); rest.remove((0, 0))
        first = next((c for c in rest if pow(r, c[0], p) != 1), None)
        if first is None: continue
        rest.remove(first)
        # second normalized element: prefer a coset of multiplicity one (two candidates a = 0, 1)
        cand2 = sorted(rest, key=lambda c: (c == (0, 0) or c == first, rest.count(c) > 1, c))
        second = cand2[0]; rest.remove(second)
        lists = [[0], [idx(0, *first)]]
        taken0 = {(0, 0), first}
        lists.append([idx(a, *second) for a in ((1,) if second in taken0 else (0, 1))])
        lines = ['L ' + ' '.join(map(str, l)) for l in lists]
        prev = None; size = len(lists[2])
        for c in sorted(rest):
            if c == prev: lines.append('='); continue
            full = [idx(a, *c) for a in range(p)]
            lines.append('L ' + ' '.join(map(str, full))); size *= p; prev = c
        out.write(f'J {nb} mu={mu} ' + ' '.join(f'{j},{z}' for j, z in cos) + '\n' + '\n'.join(lines) + '\nE\n')
        nb += 1; total += size
    out.close()
    print(f'{nb} blocks, about {total:.3g} sets (before the same-list ordering)')

main()

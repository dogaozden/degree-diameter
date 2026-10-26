#!/usr/bin/env python3
"""Coset patterns J of Haar connection sets for G = (Z_p x|_r Z_k) x Z_n, ranked by mu_J (hunt-d5; see jwalks.py).

J is the multiset of the d cosets of G' = Z_p (as (j, z) in Z_k x Z_n) met by S. With S ∋ e (translation), J contains
(0, 0). W = X0 - 3(d-1) P + (d-1)^2 delta, where P = F~ * F and X0 = P * P (F = multiplicities of J, F~(t) = F(-t),
* = convolution on Z_k x Z_n) counts the non-backtracking words of length <= 4 by coset; mu_J = sum_t p exp(-W_t / p).
Patterns are listed once per translation class (all translates that keep a point at (0,0)) and per inversion J -> -J
(S -> S^-1 swaps the two sides of the same graph).

Usage: jpatterns.py d p k r n [TOP]   prints "mu_J  (j,z) ..." for the TOP best classes (default 20) and a histogram
"""
import itertools, math, sys
import numpy as np

def main():
    d, p, k, r, n = map(int, sys.argv[1:6]); top = int(sys.argv[6]) if len(sys.argv) > 6 else 20
    cells = [(j, z) for j in range(k) for z in range(n)]; m = len(cells)
    combos = list(itertools.combinations_with_replacement(range(m), d - 1))
    F = np.zeros((len(combos), k, n))
    F[:, 0, 0] += 1
    for t, c in enumerate(combos):
        for x in c: F[t, cells[x][0], cells[x][1]] += 1
    Fh = np.fft.fft2(F); P = np.real(np.fft.ifft2(np.conj(Fh) * Fh)); X0 = np.real(np.fft.ifft2((np.conj(Fh) * Fh) ** 2))
    W = X0 - 3 * (d - 1) * P; W[:, 0, 0] += (d - 1) ** 2
    mu = (p * np.exp(-W / p)).reshape(len(combos), -1).sum(axis=1)
    seen = set(); out = []
    for t in np.argsort(mu):
        pts = [(0, 0)] + [cells[x] for x in combos[t]]
        if all(j % k == 0 for j, z in pts):
            continue                      # S inside Z_p x Z_n: (S^-1 S)^2 cannot be G
        keys = []
        for s in (1, -1):
            q = [((s * j) % k, (s * z) % n) for j, z in pts]
            for j0, z0 in set(q): keys.append(tuple(sorted(((j - j0) % k, (z - z0) % n) for j, z in q)))
        key = min(keys)
        if key in seen: continue
        seen.add(key); out.append((mu[t], key))
    print(f'# d={d} p={p} k={k} r={r} n={n}: {len(combos)} patterns with (0,0), {len(out)} classes; uniform mu '
          f'{p * k * n * math.exp(-(1 + d * (d - 1) + d * (d - 1) ** 3) / (p * k * n)):.2f}')
    hist = {}
    for v, _ in out: hist[round(v, 1)] = hist.get(round(v, 1), 0) + 1
    acc = 0
    for v in sorted(hist)[:15]: acc += hist[v]; print(f'# mu_J <= {v:.1f}: {acc} classes')
    for v, key in out[:top]: print(f'{v:.3f} ' + ' '.join(f'{j},{z}' for j, z in key))

main()

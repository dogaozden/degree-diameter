"""Check the spectrum of the incidence graph of H(q) (q = 2, 3): singular values of the point-line incidence matrix
should be q+1 (once), sqrt(3q), sqrt(q), 0.  Used by the spectral obstruction in D8_NUMEROLOGY.md §1.3."""
import numpy as np
import gh

for q in (2, 3):
    H = gh.load(q)
    N = H.N
    Inc = np.zeros((N, N))
    for k in range(N):
        for p in H.lines[k]:
            Inc[int(p), k] = 1
    s = np.linalg.svd(Inc, compute_uv=False)
    vals, cnts = np.unique(np.round(s, 6), return_counts=True)
    print(f'q={q}: singular values of the {N}x{N} incidence matrix:',
          ', '.join(f'{v:.6f} (x{c})' for v, c in zip(vals[::-1], cnts[::-1])),
          f'| expected q+1={q+1}, sqrt(3q)={np.sqrt(3*q):.6f}, sqrt(q)={np.sqrt(q):.6f}, 0')

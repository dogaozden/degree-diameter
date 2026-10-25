"""Exact intact designs for Delta=q+2 with m=q+4 copies: a bijection phi of Z_m^* with phi(a) not in {0,a} and
phi(a) = a + phi^{-1}(-a); quotient B[a][b] = 1 iff b not in {-a, -phi(a)}. For each solution print the spectrum
of B B^T on the complement of the all-ones vector (must lie in {0, q, 3q} for a real equitable partition)."""
import itertools, numpy as np, sys
for m in map(int, sys.argv[1:]):
    q = m - 4
    units = list(range(1, m))
    sols = 0; ok = 0
    # backtracking over phi
    def rec(phi, used):
        global sols, ok
        if len(phi) == len(units):
            inv = {v: k for k, v in phi.items()}
            if all(phi[a] == (a + inv[(-a) % m]) % m for a in units):
                sols += 1
                B = np.array([[0 if b in ((-a) % m, (-phi[a]) % m) else 1 for b in units] for a in units])
                ev = np.linalg.eigvalsh(B @ B.T)
                ev = sorted(set(np.round(ev, 6)))
                if all(any(abs(e - t) < 1e-6 for t in (0, q, 3 * q, (q + 1) ** 2)) for e in ev): ok += 1
            return
        a = units[len(phi)]
        for v in units:
            if v in used or v == a: continue
            phi[a] = v; used.add(v)
            rec(phi, used)
            del phi[a]; used.discard(v)
    rec({}, set())
    print('m', m, 'q', q, 'functional-equation solutions', sols, 'with admissible spectrum', ok)

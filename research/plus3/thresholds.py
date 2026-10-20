"""Finite check behind the near-copy lemma (plus3.tex, Lemma 3).

A new point h with a old lines and d new lines satisfies (Lemma 2), with t = number of
changed old incidences on its old lines and eps = 0 if t = 0 else 1:
    a >= q + 1 - l - eps,      sigma <= s := 2q + 1 + t,
and with r = the largest number of its old lines through one old point, b = a - r:
    (b+1) r <= s + 1,          r * s >= a (a - 1).
Lemma 3 claims b <= 1 whenever q >= 3l + 6 + t + 3 eps.  This script checks the claim
exhaustively for all q <= QMAX, l <= LMAX, t <= TMAX (the text proves it for large a).
"""
QMAX, LMAX, TMAX = 400, 12, 12


def bad(q, l, t):
    eps = 0 if t == 0 else 1
    s = 2 * q + 1 + t
    for a in range(max(1, q + 1 - l - eps), q + 3):
        for r in range(1, a - 1):
            b = a - r
            if b >= 2 and (b + 1) * r <= s + 1 and r * s >= a * (a - 1):
                return True
    return False


worst = 0
for t in range(TMAX + 1):
    eps = 0 if t == 0 else 1
    for l in range(0, LMAX + 1):
        q0 = 3 * l + 6 + t + 3 * eps
        fails = [q for q in range(q0, QMAX) if bad(q, l, t)]
        assert not fails, (t, l, fails[:5])
        tight = bad(q0 - 1, l, t)
        worst += tight
print(f'claim holds for all q <= {QMAX}, l <= {LMAX}, t <= {TMAX}; '
      f'threshold tight (q0-1 fails) in {worst} of {(TMAX+1)*(LMAX+1)} cases')

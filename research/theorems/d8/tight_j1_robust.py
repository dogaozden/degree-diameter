"""D8_NUMEROLOGY.md §1.5, Theorem 2: no regular one-matching guaranteed-walk design with M = q + 4 for q >= 9,
without the one-miss assumption.

Part 1 checks, on random regular labellings of H(3) and H(4) (points coloured so that every line is rainbow, lines
coloured so that every pencil is rainbow, M = 17 and 21 colours, no covering assumed), the set identities and
inequalities the proof uses:
  |A_g| = P - n_g - (q+1) m_{-g} + k_{-g},   |B_g| = P - m_g - (q+1) n_{-g} + r_g,
  N u_d = 1 - pi_{-d} - w_{-d} + kappa_d,   N^T w_{-d} = 1 - lambda_d - u_d + rho_d,
  (N^T N - I) u_d = q 1 + z_d,  z_d = lambda_d - mu_d - rho_d + nu_d,
  s_d (P - s_d) / P <= q/(q-1)^2 * |z_d - mean|^2       (s_d = number of zeros of N u_d),
  k_d = r_d, rho_d inside the support of the 0/1 vector nu_d, so z_d = lambda_d - mu_d + nu'_d with |nu'_d| = q k_d,
  |z_d|^2 <= b + |mu|^2 + |nu'| + 2<lambda,nu'>.
Part 2 is a first, cruder version (one label at a time; contradiction for q >= 11).
Part 3 is the inequality of the proof (summed over the good labels) for every case (c_A, c_B): contradiction for
every q >= 9.
"""
import random
import sys

import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402


def rainbow_colouring(groups_of, members, n, M, rng):
    """colour 0..n-1 so that every group (list of members) is rainbow; groups_of[v] = groups containing v"""
    col = -np.ones(n, dtype=np.int64)
    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        used = {int(col[w]) for g in groups_of[v] for w in members[g] if col[w] >= 0}
        free = [c for c in range(M) if c not in used]
        col[v] = rng.choice(free)
    return col


def part1(q=3, M=17, seeds=3):
    H = gh.load(q)
    P = H.N
    LINES = [list(map(int, H.lines[k])) for k in range(P)]
    THR = [list(map(int, H.through[p])) for p in range(P)]
    N = np.zeros((P, P), dtype=np.int64)  # points x lines
    for k in range(P):
        for p in LINES[k]:
            N[p, k] = 1
    NtN = N.T @ N
    gam = q / (q - 1) ** 2
    worst = 0.0
    ncoinc = [0]
    for seed in range(seeds):
        rng = random.Random(seed)
        t = rainbow_colouring(THR, LINES, P, M, rng)          # points: every line rainbow
        l = rainbow_colouring(LINES, THR, P, M, rng)          # lines: every pencil rainbow
        n = np.bincount(t, minlength=M)
        m = np.bincount(l, minlength=M)
        X = [set([int(t[x])] + [(-int(l[b])) % M for b in THR[x]]) for x in range(P)]
        Y = [set([int(l[y])] + [(-int(t[a])) % M for a in LINES[y]]) for y in range(P)]
        for g in range(1, M):
            A = np.array([g not in X[x] for x in range(P)], dtype=np.int64)
            B = np.array([g not in Y[y] for y in range(P)], dtype=np.int64)
            kap = np.array([t[x] == g and any(l[b] == (-g) % M for b in THR[x]) for x in range(P)])  # kappa_{-g}
            rho = np.array([l[y] == g and any(t[a] == (-g) % M for a in LINES[y]) for y in range(P)])  # rho_g
            assert A.sum() == P - n[g] - (q + 1) * m[(-g) % M] + kap.sum()
            assert B.sum() == P - m[g] - (q + 1) * n[(-g) % M] + rho.sum()
        for d in range(1, M):
            md = (-d) % M
            u = (l == d).astype(np.int64)
            w = (t == md).astype(np.int64)
            pi = np.array([md not in X[x] for x in range(P)], dtype=np.int64)
            lam = np.array([d not in Y[y] for y in range(P)], dtype=np.int64)
            kap = np.array([t[x] == md and any(l[b] == d for b in THR[x]) for x in range(P)], dtype=np.int64)
            rho = np.array([l[y] == d and any(t[a] == md for a in LINES[y]) for y in range(P)], dtype=np.int64)
            one = np.ones(P, dtype=np.int64)
            assert np.array_equal(N @ u, one - pi - w + kap)
            assert np.array_equal(N.T @ w, one - lam - u + rho)
            mu, nu = N.T @ pi, N.T @ kap
            z = lam - mu - rho + nu
            assert np.array_equal(NtN @ u - u, q * one + z)
            assert not np.any(lam & rho)
            s = int(P - (N @ u).sum())
            zc = z - z.mean()
            lhs, rhs = s * (P - s) / P, gam * float(zc @ zc)
            assert lhs <= rhs + 1e-9
            b, r, K = lam.sum(), rho.sum(), nu.sum()
            assert z @ z <= b + r + mu @ mu + K + 2 * (lam @ nu) + 2 * (rho @ mu)
            # Theorem 2, refined: coincidence points <-> coincidence lines, rho inside supp(nu), z = lam - mu + nu'
            assert kap.sum() == rho.sum() and nu.max() <= 1 and np.all(nu[rho == 1] == 1)
            nup = nu - rho
            assert nup.sum() == q * kap.sum() and np.array_equal(z, lam - mu + nup)
            assert z @ z <= b + mu @ mu + nup.sum() + 2 * (lam @ nup)
            ncoinc[0] += int(kap.sum())
            if rhs > 0:
                worst = max(worst, lhs / rhs)
    print(f'part 1: q={q}, M={M}, {seeds} random regular labellings: all identities hold '
          f'({ncoinc[0]} coincidence points in all); max of LHS/RHS in the spectral inequality {worst:.3f}')


def part3():
    """the summed version (the proof in D8_NUMEROLOGY.md): for every case (c_A, c_B), with P = 1,
    LHS = (q-1)/(q+1) * (2 - (c_B + 2 c_A)/(q+1))  must exceed
    RHS = q/(q-1)^2 * ( X(1 - X/(q+3)) + 4 beta + 2 q S ),  X = q + 1 - c_A - beta,  beta = 1 + S0,
    S = S0 = (2 - c_A - c_B)/(q+1)   (needs X >= (q+3)/2)."""
    print('part 3: summed inequality (the proof); "ok" = contradiction in every case (c_A, c_B)')
    print('  q   worst case   RHS      LHS      ok')
    first = None
    for q in list(range(5, 32)) + [64, 128, 1024]:
        worst = None
        allok = True
        for cA in range(3):
            for cB in range(3 - cA):
                S = (2 - cA - cB) / (q + 1)
                beta = 1 + S
                X = q + 1 - cA - beta
                rhs = q / (q - 1) ** 2 * (X * (1 - X / (q + 3)) + 4 * beta + 2 * q * S)
                lhs = (q - 1) / (q + 1) * (2 - (cB + 2 * cA) / (q + 1))
                ok = X >= (q + 3) / 2 and rhs < lhs
                allok &= ok
                if worst is None or rhs - lhs > worst[0]:
                    worst = (rhs - lhs, cA, cB, rhs, lhs)
        if allok and first is None:
            first = q
        _, cA, cB, rhs, lhs = worst
        print(f'{q:4d}   ({cA}, {cB})       {rhs:.4f}   {lhs:.4f}   {allok}')
    bad = []
    for q in range(9, 100001):
        for cA in range(3):
            for cB in range(3 - cA):
                S = (2 - cA - cB) / (q + 1)
                beta = 1 + S
                X = q + 1 - cA - beta
                rhs = q / (q - 1) ** 2 * (X * (1 - X / (q + 3)) + 4 * beta + 2 * q * S)
                lhs = (q - 1) / (q + 1) * (2 - (cB + 2 * cA) / (q + 1))
                if not (X >= (q + 3) / 2 and rhs < lhs):
                    bad.append((q, cA, cB))
    print(f'every integer q in [9, 100000], all (c_A, c_B): contradiction fails for {len(bad)} cases {bad[:5]}')


def part2():
    print('part 2: final inequality (P = 1); "ok" = contradiction, i.e. no design')
    print('  q   worst case (c_A, c_B)   upper bound   lower bound   ok   analytic 0.33 + 15.4/(q-1)')
    for q in [5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 64, 128, 1024]:
        pre = (q + 1) * q / (q - 1) ** 3
        worst = None
        for cA in range(3):
            for cB in range(3 - cA):
                S = (2 - cA - cB) / (q + 1)
                up = pre * ((q + 3) * (0.25 + 2 / (q + 1)) + (4 * (q + 1) + 2) * S)
                lo = 2 - (cB + 2 * cA) / (q + 1)
                if worst is None or up - lo > worst[0]:
                    worst = (up - lo, cA, cB, up, lo)
        _, cA, cB, up, lo = worst
        an = 0.33 + 15.4 / (q - 1) if q >= 11 else float('nan')
        print(f'{q:4d}   ({cA}, {cB})                  {up:.4f}        {lo:.4f}        {up < lo}   {an:.4f}')
    # every integer 11 <= q <= 10^5, all cases
    bad = []
    for q in range(11, 100001):
        pre = (q + 1) * q / (q - 1) ** 3
        for cA in range(3):
            for cB in range(3 - cA):
                S = (2 - cA - cB) / (q + 1)
                up = pre * ((q + 3) * (0.25 + 2 / (q + 1)) + (4 * (q + 1) + 2) * S)
                if up >= 2 - (cB + 2 * cA) / (q + 1):
                    bad.append((q, cA, cB))
    print(f'every integer q in [11, 100000], all (c_A, c_B): contradiction fails for {len(bad)} cases {bad[:5]}')


if __name__ == '__main__':
    part1(3, 17)
    part1(4, 21, 2)
    part2()
    part3()

"""Effort law check (BEYOND_RANDOM §2): for every orbit run log, mu_A from the clumped model and the predicted evals
1e5 exp((mu_A - 13)/2), against the evals the run used (solved) or spent (unsolved).
usage: python3 effort_check.py LOG...   (haar_sym ORBIT logs; RESULT line + 'ORBIT k=..: |Fix(alpha)| = ..' line)
Columns: cell, group, k, f, |Fix|, mu, phi, mu_A, predicted evals, actual evals, solved?, ln(actual/predicted).
mu_A = (mu - |Fix| e^-lam)/k + phi; phi = fixed elements at rate lam/k (fixed involutions at odd D: lam/2k, weight 2);
at odd D in characteristic 2 the q^2 - 1 involutions outside Fix add 2 (q^2-1)/k e^(-lam/2) (they pair with themselves)."""
import sys, re, math
def W(d, D):
    if D % 2: kk = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, kk + 1))
    kk = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(kk))
def fixinv(fam, q, frob, D):
    """fixed involutions (excl. e) and involutions outside Fix, per the alpha type."""
    if frob:                                        # Fix = Q(2, q0), q0 = p^(e/k); only char 2 used here
        return (3, q * q - 1 - 3) if q % 2 == 0 else (1, 0)
    if fam == 'sl': return (1, 0) if q % 2 else (0, q * q - 1)
    if fam == 'psl': return (1, 0)                  # torus of even order has one involution (approximation)
    return (1, 0)
rows = []
for path in sys.argv[1:]:
    txt = open(path, errors='replace').read()
    r = re.search(r'RESULT d=(\d+) D=(\d+) group=(.*?) N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+) orbit k=(\d+) m=(\d+) f=(\d+) fix=(\d+)', txt)
    if not r: continue
    d, D, grp, N, best, ev, t, k, m, f, fix = r.groups(); d, D, N, best, ev, k, f, fix = map(int, (d, D, N, best, ev, k, f, fix))
    g = grp.split(); fam = g[0] if g[0] != 'prod' else 'prod'; q = int(g[1]) if g[0] != 'prod' else 0
    frob = 'Frobenius' in txt
    lam = W(d, D) / N; mu = N * math.exp(-lam); F = fix + 1
    finv, oinv = fixinv(fam, q, frob, D) if fam != 'prod' else (0, 0)
    if D % 2:
        n = int(re.search(r'x Z_(\d+)', grp).group(1)) if 'x Z_' in grp else 1
        oinv_tot = oinv * (1 if n % 2 else 2)
        phi = (fix - finv) * math.exp(-lam / k) + 2 * finv * math.exp(-lam / (2 * k)) + 2 * oinv_tot / k * math.exp(-lam / 2)
    else: phi = fix * math.exp(-lam / k)
    muA = (mu - F * math.exp(-lam)) / k + phi
    pred = 1e5 * math.exp((muA - 13) / 2)
    orbw = re.search(r'ORBW=(\d+)', txt)
    rows.append(((d, D), grp, k, f, fix, mu, phi, muA, pred, ev, best == 0, math.log(ev / pred), path.split('/')[-1], orbw.group(1) if orbw else ''))
print('| cell | group | k | f | Fix | mu | phi | mu_A | predicted evals | evals | result | ln(evals/pred) |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|')
for r in sorted(rows, key=lambda r: (r[0][1], r[0][0], r[5])):
    print('| (%d,%d) | %s%s | %d | %d | %d | %.1f | %.2f | %.2f | %.2g | %.2g | %s | %+.1f |' % (r[0] + (r[1], ' ORBW=%s' % r[13] if r[13] else '', r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], 'solved' if r[10] else 'unsolved', r[11])))
sol = [r[11] for r in rows if r[10]]
if sol: print('\nsolved: %d runs, mean ln(evals/pred) %+.2f, sd %.2f' % (len(sol), sum(sol) / len(sol), (sum((x - sum(sol) / len(sol)) ** 2 for x in sol) / max(1, len(sol) - 1)) ** 0.5))

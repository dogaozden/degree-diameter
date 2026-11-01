# Tail of the chain-minimum distribution (ORBW=3 chains, pooled from unique grind logs).
# Energies are multiples of 3 (one orbit or one fixed element = 3); m = energy/3.
# Model: P(min <= m) = A * exp(lam * m) for small m (exponential lower tail), fitted by weighted LS on
# ln(cumulative count) with weights = cumulative count (Poisson), using m in [mlo, mhi].
import csv, math, collections, sys
def load(path, grp_sub):
    mins = []; cpu = 0.0; n = 0
    for r in csv.DictReader(open(path), delimiter='\t'):
        if grp_sub in r['group']:
            mins.append(int(r['min']) // 3); cpu += int(r['secs']); n += 1
    return mins, cpu / 3600.0
def fit(mins, mlo, mhi):
    n = len(mins)
    cum = {m: sum(1 for x in mins if x <= m) for m in range(0, 12)}
    pts = [(m, cum[m]) for m in range(mlo, mhi + 1) if cum[m] > 0]
    # weighted least squares of ln(cum) on m, weight = cum (Poisson)
    W = sum(c for _, c in pts); mx = sum(m * c for m, c in pts) / W; my = sum(c * math.log(c) for _, c in pts) / W
    b = sum(c * (m - mx) * (math.log(c) - my) for m, c in pts) / sum(c * (m - mx) ** 2 for m, c in pts)
    a = my - b * mx
    return a, b, cum
for label, sub in (('psl 23 x Z_97', 'psl 23'), ('prod psl 7 sl 8 x Z_7', 'prod psl 7')):
    mins, cpu = load(sys.argv[1], sub)
    n = len(mins)
    for mlo, mhi in ((1, 4), (2, 5), (2, 6), (3, 7)):
        a, b, cum = fit(mins, mlo, mhi)
        p0 = math.exp(a)          # extrapolated P(min <= 0) per descent
        print(f'{label} n={n} fit m={mlo}..{mhi}: lam={b:.2f} per unit (factor {math.exp(b):.2f}), '
              f'P(m<=0) ~ {p0:.2e} (1 in {1/p0:,.0f}), P(m<=1) ~ {math.exp(a+b):.2e}')
    print('  empirical P(m<=k):', ' '.join(f'{k}:{cum[k]/n:.2e}' for k in range(0, 8)))
    print(f'  per CPU-hour (chains={n}, cpu {cpu:.1f} h): P(m<=0) ~ {p0 * n / cpu:.4f}/h ... 1 cost-0 per {1/(p0*n/cpu):,.0f} CPU-h (extrapolated)')

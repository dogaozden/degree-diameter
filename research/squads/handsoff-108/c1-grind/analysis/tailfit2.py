# Lower-tail fit of the ORBW=3 chain-minimum distribution (m = energy/3; all minima are multiples of 3).
# Method A: log-linear least squares of ln(cumulative count) on m over a window [mlo, mhi] (weights = counts),
#           extrapolated to m=0 (P(energy 0) = A/n).
# Method B: pure ratio (geometric) estimate: r = n(m+1)/n(m) averaged over the window, P(m=0) = P(m=1)/r.
import csv, math, sys
def load(path, sub):
    mins, cpu, n = [], 0.0, 0
    for r in csv.DictReader(open(path), delimiter='\t'):
        if sub in r['group']:
            mins.append(int(r['min']) // 3); cpu += int(r['secs']); n += 1
    return mins, cpu / 3600.0
for label, sub in (('psl 23 x Z_97', 'psl 23'), ('prod psl 7 sl 8 x Z_7', 'prod psl 7')):
    mins, cpu = load(sys.argv[1], sub); n = len(mins)
    cnt = {m: sum(1 for x in mins if x == m) for m in range(0, 12)}
    cum = {m: sum(1 for x in mins if x <= m) for m in range(0, 12)}
    print(f'{label}: chains={n}, cpu={cpu:.1f} h, mean secs/chain={3600*cpu/n:.0f}')
    print('  counts m=1..6:', [cnt[m] for m in range(1, 7)], ' P(m<=k):', ' '.join(f'{k}:{cum[k]/n:.1e}' for k in (1, 2, 3)))
    for mlo, mhi in ((1, 3), (1, 4), (2, 4), (2, 5)):
        pts = [(m, cum[m]) for m in range(mlo, mhi + 1) if cum[m] > 0]
        W = sum(c for _, c in pts); mx = sum(m * c for m, c in pts) / W
        my = sum(c * math.log(c) for _, c in pts) / W
        b = sum(c * (m - mx) * (math.log(c) - my) for m, c in pts) / sum(c * (m - mx) ** 2 for m, c in pts)
        a = my - b * mx
        p0 = math.exp(a) / n
        print(f'  A window {mlo}..{mhi}: slope {b:.2f}/unit (x{math.exp(b):.1f}), P(energy 0) ~ {p0:.1e} = 1 in {1/p0:,.0f} descents')
    ratios = [cnt[m + 1] / cnt[m] for m in range(1, 4) if cnt[m] > 0]
    if ratios and cnt[1] > 0:
        r = math.exp(sum(math.log(x) for x in ratios) / len(ratios))
        p1 = cnt[1] / n
        print(f'  B ratios n(m+1)/n(m) for m=1..3: {[round(x,2) for x in ratios]}, geo mean {r:.2f}; P(energy 0) ~ P(m=1)/r = {p1/r:.1e} = 1 in {r/p1:,.0f}')
    rate = n / cpu
    print(f'  chains per CPU-hour {rate:.1f}; if P0 = 5e-5..1e-4: one energy-0 per {1/(1e-4*rate):,.0f}..{1/(5e-5*rate):,.0f} CPU-h')

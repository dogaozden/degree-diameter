# Appendix B odd-D claims: unlimited odd cells (largest scanned q has diameter > D) and comparison with the Thm 3.2 limit.
import re, glob
import qlib as L
def first_kv(line):
    kv = {}
    for k, v in re.findall(r'(\w+)=([^\s()]+)', line): kv.setdefault(k, v)
    return kv
rows = {}
for f in sorted(glob.glob('/home/user/degree-diameter/research/theorems/haar_families/scan/lps_p*.txt')):
    for line in open(f):
        if not line.startswith('p='): continue
        kv = first_kv(line); p = int(kv['p']); q = int(kv['q']); D = int(kv['diameter'])
        rows.setdefault(p, {})[q] = D
for p in sorted(rows):
    qs = sorted(rows[p]); qmax = qs[-1]
    for D in range(5, 13, 2):
        lim = max([r for r in L.primes(p+1, 5000) if r*r < 2*p**(D//2)], default=None)
        ok = [r for r in qs if rows[p][r] <= D]
        if not ok: continue
        big = max(ok)
        unlimited = rows[p][qmax] > D
        # is there any q above big with diam<=D? (monotone check)
        above = [r for r in qs if r > big and rows[p][r] <= D]
        print("Delta=%d D=%d lim=%d largest_q_diam<=D=%d unlimited=%s  scan_max_q=%d diam_at_scan_max=%d  #q_above_with_diam<=D=%d" %
              (p+1, D, lim, big, unlimited, qmax, rows[p][qmax], len(above)))

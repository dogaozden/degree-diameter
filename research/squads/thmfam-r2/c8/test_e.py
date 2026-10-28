# Appendix B / summary numbers: largest LPS graph (scan lines) with diameter <= D, Thm 3.2 q-limit, table ratios (own code).
import re, glob
import qlib as L
def first_kv(line):
    kv = {}
    for k, v in re.findall(r'(\w+)=([^\s()]+)', line): kv.setdefault(k, v)
    return kv
best = {}; allrows = []
for f in sorted(glob.glob('/home/user/degree-diameter/research/theorems/haar_families/scan/lps_p*.txt')):
    for line in open(f):
        if not line.startswith('p='): continue
        kv = first_kv(line); p = int(kv['p']); q = int(kv['q']); n = int(kv['vertices']); D = int(kv['diameter']); m = int(kv['m'])
        allrows.append((p, q, n, D, m, f.split('/')[-1]))
table = {(4,8):2184,(4,9):4970,(4,10):11748,(6,8):29790,(6,9):117360,(6,10):452032,(8,8):201480,(8,9):1091232,(8,10):6927210,(12,8):4650100,(12,9):30001152,(14,8):14172480,(14,9):95087738}
scanmax = {}
for p in [3,5,7,11,13]:
    rows = [r for r in allrows if r[0]==p]
    scanmax[p] = (max(r[1] for r in rows), max(r[2] for r in rows))
    for D in range(4, 12):
        cand = [r for r in rows if r[3] <= D]
        if not cand: continue
        bq = max(cand, key=lambda r: r[2])
        best[(p+1, D)] = (bq[1], bq[2])
print("scan max q per p:", scanmax)
for key in sorted(best):
    Delta, D = key
    q, n = best[key]
    t = table.get((Delta, D))
    line = "Delta=%d D=%d largest LPS q=%d n=%d" % (Delta, D, q, n)
    if t: line += " table=%d ratio table/LPS=%.2f" % (t, t/n)
    print(line)
# Thm 3.2 limit and whether largest scanned q equals it at odd D
print("--- Thm 3.2 q-limit (largest prime q with q^2 < 2 p^floor(D/2)) vs largest q with diam<=D in scan")
for p in [3,5,7,11,13]:
    for D in range(6, 12):
        lim = max([r for r in L.primes(p+1, 5000) if r*r < 2*p**(D//2)], default=None)
        rows = [r for r in allrows if r[0]==p and r[3] <= D]
        if not rows: continue
        qmax = max(r[1] for r in rows)
        scanned_max = max(r[1] for r in allrows if r[0]==p)
        if D % 2 == 1:
            print("p=%d D=%d limit=%d largest q with diam<=D: %d  (scan max q for p: %d)" % (p, D, lim, qmax, scanned_max))
# sanity: diameters in scan are monotone? (no) ; check n = q(q^2-1)m
bad = [r for r in allrows if r[2] != r[1]*(r[1]**2-1)*r[4]]
print("lines with vertices != q(q^2-1)m:", len(bad))

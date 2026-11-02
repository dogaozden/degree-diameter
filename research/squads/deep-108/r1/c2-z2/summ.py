import sys, statistics
# usage: summ.py samp.tsv  -> stats of "M id osz uBA uAA uBB z..." lines
rows = []
for line in open(sys.argv[1]):
    f = line.split()
    if len(f) < 10 or f[0] != 'M': continue
    uBA, uAA, uBB = int(f[3]), int(f[4]), int(f[5])
    rows.append((uBA, uAA, uBB, f))
n = len(rows)
conn = [r for r in rows if r[0] + r[1] <= 300]
withB = [r for r in rows if r[2] >= 0]
C = sorted(r[0] + r[1] + r[2] for r in withB)
if not rows:
    print("empty"); sys.exit()
med = lambda v: statistics.median(v) if v else float('nan')
ua = sorted(r[0] + r[1] for r in rows)
print(f"n={n} connected(uBA+uAA<=300)={len(conn)} withB={len(withB)} minC={C[0] if C else 'NA'} "
      f"p10C={C[len(C)//10] if C else 'NA'} medC={med(C):.0f} medUA={med(ua):.0f} minUA={ua[0]}")
best = sorted(withB, key=lambda r: r[0] + r[1] + r[2])[:10]
for r in best:
    print("  best C=%d uBA=%d uAA=%d uBB=%d z=%s" % (r[0] + r[1] + r[2], r[0], r[1], r[2], " ".join(r[3][6:11])))

# usage: python3 tailfit.py out/<name>.out h  -> units table: quantiles and empirical lower tail
import re, sys, statistics, math
path, h = sys.argv[1], int(sys.argv[2])
Cs = []
for l in open(path):
    m = re.search(r" C (\d+) conn (\d)", l)
    if m and m.group(2) == "1": Cs.append(int(m.group(1)))
Cs.sort(); n = len(Cs)
u = [c / h for c in Cs]
def qq(p): return u[min(n - 1, int(p * (n - 1) + 0.5))]
print("n=%d min=%.1f p5=%.1f p10=%.1f p25=%.1f med=%.1f p75=%.1f max=%.1f (units of h)" % (n, u[0], qq(.05), qq(.10), qq(.25), qq(.5), qq(.75), u[-1]))
for x in (10, 12, 15, 20):
    k = sum(1 for v in u if v <= x)
    print("  frac(C/h <= %d) = %d/%d = %.3f" % (x, k, n, k / n))

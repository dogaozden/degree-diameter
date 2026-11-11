import math, sys
d, D = 4, 10
W = d * sum((d - 1) ** (2 * i) for i in range(D // 2))
rows = []
for line in open(sys.argv[1]):
    f = line.rstrip("\n").split("\t")
    if f[2] == "ERR": continue
    N, spec = int(f[0]), f[1]; mn, p10, med = int(f[2]), int(f[3]), int(f[4])
    mu = N * math.exp(-W / N)
    rows.append(((p10 + med) / mu, N, spec, mn, p10, med))
rows.sort()
top = int(sys.argv[2]) if len(sys.argv) > 2 else 40
for r in rows[:top]:
    print("%.3f  N=%d  %-26s min=%d p10=%d med=%d" % (r[0], r[1], r[2], r[3], r[4], r[5]))
print("total", len(rows))

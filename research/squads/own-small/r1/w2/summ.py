import sys, collections
# summ.py label file: prints n, invalid fraction, min, #min, 5% quantile, median over valid lines
vals = []; inv = 0; n = 0
for line in open(sys.argv[2]):
    s = line.strip(); n += 1
    if s == "invalid" or s == "": inv += 1; continue
    vals.append(int(s))
vals.sort()
q = lambda p: vals[int(p * (len(vals) - 1))] if vals else -1
mn = vals[0] if vals else -1
c = collections.Counter(vals)
print(f"{sys.argv[1]} n={n} inv={inv/n:.3f} min={mn} n_min={c[mn]} q01={q(0.01)} q05={q(0.05)} med={q(0.5)}")

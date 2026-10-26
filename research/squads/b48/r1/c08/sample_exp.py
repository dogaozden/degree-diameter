import random, re, sys
random.seed(int(sys.argv[1]))
rows = []
for line in open("j20.txt"):
    mn = int(line.split()[0]); J = [int(x) for x in re.search(r"J=\((.*?)\)", line).group(1).split(",")]
    rows.append((mn, J))
strata = {"bal": [J for mn, J in rows if mn >= 157], "mid": [J for mn, J in rows if 146 <= mn <= 150], "low": [J for mn, J in rows if mn <= 130]}
out = []
for name, n in [("bal", 8), ("mid", 8), ("low", 8)]:
    for J in random.sample(strata[name], min(n, len(strata[name]))):
        out.append((name, J))
for name, J in out:
    print(name, ",".join(str(x) for x in J[1:]))

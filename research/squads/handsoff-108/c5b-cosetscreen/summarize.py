# Summarise out/*.out (cscreen output) into a ranked table. Usage: python3 summarize.py [out_dir]
import glob, os, re, sys, math, statistics
from math import comb
OUT = sys.argv[1] if len(sys.argv) > 1 else "out"
fams = []
for path in sorted(glob.glob(os.path.join(OUT, "*.out"))):
    name = os.path.basename(path)[:-4]
    rows = []
    for line in open(path):
        m = re.match(r"cand (\d+) reps (.*) uncBA (\d+) uncAA (\d+) uncBB (\d+) C (\d+) conn (\d) ecc (\d+)", line)
        if m:
            rows.append(dict(i=int(m.group(1)), uA=int(m.group(3)), uAA=int(m.group(4)), uBB=int(m.group(5)),
                             C=int(m.group(6)), conn=int(m.group(7)), ecc=int(m.group(8))))
    errp = os.path.join(OUT, name + ".err")
    hdr = {}
    if os.path.exists(errp):
        for line in open(errp):
            if line.startswith("q="):
                hdr["dc"] = line.strip()
                hdr["N"] = int(re.search(r"N=(\d+)", line).group(1))
                hdr["h"] = int(re.search(r"h=(\d+)", line).group(1))
                cs = dict((int(a), int(b)) for a, b in re.findall(r" c(\d+):(\d+)", line))
                hdr["cs"] = cs
            if line.startswith("W="):
                hdr["mu"] = float(re.search(r"mu\(vertex Poisson\)=([\d.]+)", line).group(1))
    if not rows or "N" not in hdr:
        continue
    h, N, mu = hdr["h"], hdr["N"], hdr["mu"]
    Cs = sorted(r["C"] for r in rows)
    uA = sorted(r["uA"] for r in rows)
    n = len(Cs)
    def q(xs, p):
        return xs[min(n - 1, int(p * (n - 1) + 0.5))]
    med = statistics.median(Cs)
    conn = sum(r["conn"] for r in rows) / n
    zeros = sum(1 for c in Cs if c == 0)
    # family size from the spec in the name is not known here; read it from the err "spec" line if present
    fams.append(dict(name=name, n=n, N=N, h=h, mu=mu, mu_h=mu / h, min=Cs[0], p10=q(Cs, 0.10), med=med,
                     min_units=Cs[0] / h, med_units=med / h, tax=med / mu, conn=conn, zeros=zeros,
                     uA_med=statistics.median(uA), dc=hdr["dc"]))
fams.sort(key=lambda f: (f["med"] if f["conn"] > 0.5 else 1e18))
print("name\tn\tN\th\tmu\tmu/h\tmin_C\tp10_C\tmed_C\tmin/h\tmed/h\ttax=med/mu\tconn\tC=0")
for f in fams:
    print("%s\t%d\t%d\t%d\t%.1f\t%.2f\t%d\t%d\t%.0f\t%.1f\t%.2f\t%.2f\t%.2f\t%d" % (
        f["name"], f["n"], f["N"], f["h"], f["mu"], f["mu_h"], f["min"], f["p10"], f["med"],
        f["min_units"], f["med_units"], f["tax"], f["conn"], f["zeros"]))

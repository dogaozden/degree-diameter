# A5 screen parser: reads randorb_frob<j>_d.log (haar_sym RANDORB output), prints one comparable row per run.
import re, sys, os
A = "/home/user/degree-diameter/research/squads/d11D10-r2/A5"
def parse(path):
    txt = open(path).read()
    r = {"file": os.path.basename(path)}
    m = re.search(r"ORBIT k=10 m=1 f=1: \|Fix\(alpha\)\| = (\d+)", txt)
    r["fix"] = int(m.group(1)) if m else None
    m = re.search(r"^RANDORB d=.*$", txt, re.M)
    if not m:
        r["status"] = "no RANDORB line"; return r
    line = m.group(0)
    for k, v in re.findall(r"(\w+)=([-\d.]+)", line):
        if k in ("samples", "min", "p1", "p10", "median", "mean", "var", "mu", "time", "fix"):
            r[k] = float(v)
    h = re.search(r"RANDORB hist \(cost/k\):((?: \d+)+)", txt)
    hist = [int(x) for x in h.group(1).split()]
    r["hist"] = hist
    deg = hist[31]; nd = hist[:31]; ndn = sum(nd)
    r["deg"] = deg; r["deg_frac"] = deg / sum(hist)
    r["nd_n"] = ndn
    if ndn:
        r["nd_mean_clumps"] = sum(i * c for i, c in enumerate(nd)) / ndn
        acc = 0; med = None
        for i, c in enumerate(nd):
            acc += c
            if med is None and acc * 2 >= ndn: med = i
        r["nd_median_clumps"] = med
        acc = 0; lo = None
        for i, c in enumerate(nd):
            if c: lo = i; break
        r["nd_min_clumps"] = lo
    c0 = re.search(r"cost counts 0\.\.40:((?: \d+)+)", txt)
    if c0:
        cc = [int(x) for x in c0.group(1).split()]
        r["low_costs"] = [(c, n) for c, n in enumerate(cc) if n]
    return r
rows = [parse(os.path.join(A, f"randorb_frob{j}_d.log")) for j in (1, 2, 3, 4)
        if os.path.exists(os.path.join(A, f"randorb_frob{j}_d.log"))]
for r in rows:
    print(r["file"], "fix=", r.get("fix"), "samples=", r.get("samples"), "time=", r.get("time"))
    if "hist" not in r:
        print("   ", r.get("status", "no data yet")); continue
    print("    min=%s p1=%s p10=%s median=%s  mu=%s" % (r.get("min"), r.get("p1"), r.get("p10"), r.get("median"), r.get("mu")))
    print("    degenerate (cost/k>=31) = %d of %d = %.3f" % (r["deg"], sum(r["hist"]), r["deg_frac"]))
    if r["nd_n"]:
        print("    non-degenerate n=%d  mean cost/10=%.2f  median cost/10=%s  min cost/10=%s" % (
            r["nd_n"], r["nd_mean_clumps"], r["nd_median_clumps"], r["nd_min_clumps"]))
    print("    hist cost/10 (0..30):", " ".join(str(x) for x in r["hist"][:31]))
    if "low_costs" in r: print("    exact costs <= 40 (cost,count):", r["low_costs"])

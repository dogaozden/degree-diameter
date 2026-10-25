# A1 analysis: per-sample costs of the six RANDORB=150 screens (run with RANDB=1000000: degenerate = aborted at 10^6).
import re, sys, statistics, os
DIR = "/home/user/degree-diameter/research/squads/d11D10-r2/A1"
RANDBV = 1000000
TAGS = ["afrob1_ar2", "afrob2_ar2", "afrob3_ar2", "afrob4_ar2", "afrob1_ar6", "afrob1_ar7"]
res = {}
for tag in TAGS:
    path = os.path.join(DIR, "randorb_%s.log" % tag)
    if not os.path.exists(path):
        continue
    txt = open(path).read()
    seq = [int(m.group(2)) for m in re.finditer(r"^SAMPLE (\d+) (-?\d+)$", txt, re.M)]
    stock = re.search(r"RANDORB d=.*?samples=(\d+) min=(\d+) p1=(\d+) p10=(\d+) median=(\d+) mean=([\d.]+).*?mu=([\d.]+) time=([\d.]+)", txt)
    fixl = re.search(r"\|Fix\(alpha\)\| = (\d+)", txt)
    hist = re.search(r"RANDORB hist \(cost/k\):((?: \d+)+)", txt)
    c0 = re.search(r"cost counts 0\.\.40:((?: \d+)+)", txt)
    res[tag] = dict(seq=seq, stock=stock.groups() if stock else None, fix=int(fixl.group(1)) if fixl else None,
                    hist=[int(x) for x in hist.group(1).split()] if hist else None,
                    c0=[int(x) for x in c0.group(1).split()] if c0 else None, done=("RANDORB d=" in txt))
    # consistency with the stock output
    r = res[tag]
    if stock and seq:
        assert len(seq) == int(stock.group(1)), (tag, len(seq))
        s = sorted(seq)
        assert s[0] == int(stock.group(2)) and s[len(s)//2] == int(stock.group(5)), tag
        assert abs(sum(seq) / len(seq) - float(stock.group(6))) < 0.01, tag

def stats(seq):
    nd = [c for c in seq if c < RANDBV]
    dg = len(seq) - len(nd)
    out = dict(n=len(seq), degen=dg, frac=dg / len(seq) if seq else float('nan'))
    if nd:
        out.update(nd_min=min(nd), nd_mean=statistics.mean(nd), nd_median=statistics.median(nd),
                   nd_sd=statistics.pstdev(nd), nd_p10=sorted(nd)[len(nd)//10])
        h = [0] * 32
        for c in nd: h[min(c // 10, 31)] += 1
        out["hist_nd"] = h
    return out

print("| pairing | |Fix(alpha)| | samples | degenerate (cost>1e6) | nondeg min | nondeg median | nondeg mean | nondeg sd | nondeg p10 | cost0 |")
print("|---|---|---|---|---|---|---|---|---|---|")
rows = []
for tag in TAGS:
    if tag not in res: continue
    r = res[tag]; st = stats(r["seq"])
    cost0 = r["c0"][0] if r["c0"] else 0
    print("| %s | %s | %d | %d (%.1f %%) | %d | %.1f | %.2f | %.2f | %d | %d |" % (
        tag, r["fix"], st["n"], st["degen"], 100 * st["frac"], st["nd_min"], st["nd_median"], st["nd_mean"], st["nd_sd"], st["nd_p10"], cost0))
    rows.append((tag, st))
print()
print("Non-degenerate histogram of cost/10 (bin 31 = cost >= 310):")
for tag, st in rows:
    print("%-12s %s" % (tag, " ".join(str(x) for x in st["hist_nd"])))
print()
print("Stock RANDORB stats lines (all samples incl. degenerate at 1e6), for cross-check:")
for tag in TAGS:
    if tag in res and res[tag]["stock"]:
        g = res[tag]["stock"]; print("%-12s samples=%s min=%s p1=%s p10=%s median=%s mean=%s mu=%s time=%ss" % ((tag,) + g))
print()
# equivalence checks (group-equal automorphisms with the same seed must give identical sample sequences)
for a, b in [("afrob1_ar6", "afrob4_ar2"), ("afrob1_ar7", "afrob3_ar2")]:
    if a in res and b in res and res[a]["seq"] and res[b]["seq"]:
        sa, sb = res[a]["seq"], res[b]["seq"]
        n = min(len(sa), len(sb))
        diff = sum(1 for i in range(n) if sa[i] != sb[i])
        print("equivalence %s vs %s: %d samples compared, %d differ" % (a, b, n, diff))

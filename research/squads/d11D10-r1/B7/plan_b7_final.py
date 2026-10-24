"""B7 final tables: per-family frontier and top-10 structure-safe runs (corrected model, x <= 0.03, hours <= 4)."""
import math, sys
sys.argv = ['x']
exec(open('plan_b7_corr.py').read().split("print(\"K'_3")[0])   # reuse rows/res/est from plan_b7_corr.py
safe = [r for r in res if r["x"] <= 0.03]
def name(r):
    return ("%s(2,%d)" % (r["fam"], r["p"])) if r["sym"] == "conj" else ("%s(2,%d) frob" % (r["fam"], {"SL": 32, "PSL": 243}[r["fam"]]))
print("# per family, largest vertices with hours <= 4: raw (no structure check) | corrected, x <= 0.03")
for key in sorted({(r["sym"], r["fam"], r["k"]) for r in res}):
    rs = [r for r in res if (r["sym"], r["fam"], r["k"]) == key]
    raw = [r for r in rs if r["raw"][3] <= BUD]
    cs = [r for r in rs if r["x"] <= 0.03 and r["corr"][3] <= BUD]
    rb = max(raw, key=lambda r: r["N"]) if raw else None
    cb = max(cs, key=lambda r: r["N"]) if cs else None
    s = "%-12s k=%d | " % (key[0] + "/" + key[1], key[2])
    s += ("raw %d (%s n=%d, h=%.2f, x=%.3f)" % (2 * rb["N"], name(rb), rb["n"], rb["raw"][3], rb["x"])) if rb else "raw none"
    s += " | "
    s += ("corr-safe %d (%s n=%d, h=%.2f, muA=%.2f)" % (2 * cb["N"], name(cb), cb["n"], cb["corr"][3], cb["corr"][1])) if cb else "corr-safe none"
    print(s)
print()
top = sorted(cs_all := [r for r in safe if r["corr"][3] <= BUD], key=lambda r: -r["N"])[:10]
print("# top 10 structure-safe runs (corrected hours <= 4)")
for i, r in enumerate(top, 1):
    print("%2d | %s k=%d n=%d | vert=%d N=%d | |H|=%d F=%d | mu=%.2f | muA raw=%.2f corr=%.2f | evals raw=%.3g corr=%.3g | hours raw=%.2f corr=%.2f | x=%.3f" % (
        i, name(r), r["k"], r["n"], 2 * r["N"], r["N"], r["H"], r["F"], r["raw"][0], r["raw"][1], r["corr"][1],
        r["raw"][2], r["corr"][2], r["raw"][3], r["corr"][3], r["x"]))

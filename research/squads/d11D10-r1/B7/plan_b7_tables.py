"""Emit the markdown rows for plan.md from the B7 model (same formulas as plan_b7_corr.py)."""
import sys
exec(open('plan_b7_corr.py').read().split("print(\"K'_3")[0])
def name(r):
    return ("%s(2,%d) x Z%d" % (r["fam"], r["p"], r["n"])) if r["sym"] == "conj" else ("%s(2,%d) x Z%d [Frobenius]" % (r["fam"], {"SL": 32, "PSL": 243}[r["fam"]], r["n"]))
safe = sorted([r for r in res if r["x"] <= 0.03 and r["corr"][3] <= BUD], key=lambda r: -r["N"])[:10]
print("| # | group | k | N | vertices | mu | mu_A raw | mu_A corr | evals raw | hours raw | hours corr | x |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|")
for i, r in enumerate(safe, 1):
    print("| %d | %s | %d | %d | %d | %.1f | %.2f | %.2f | %.2g | %.2f | %.2f | %.3f |" % (
        i, name(r), r["k"], r["N"], 2 * r["N"], r["raw"][0], r["raw"][1], r["corr"][1], r["raw"][2], r["raw"][3], r["corr"][3], r["x"]))
print()
print("| family | k | best N (vertices) under card model, no class check | hours | best structure-safe (x<=0.03) | hours raw / corr |")
print("|---|---|---|---|---|---|")
for key in [("conj", "PSL", 3), ("conj", "SL", 3), ("conj", "PSL", 5), ("conj", "SL", 5), ("frob", "SL", 5), ("frob", "PSL", 5)]:
    rs = [r for r in res if (r["sym"], r["fam"], r["k"]) == key]
    raw = [r for r in rs if r["raw"][3] <= BUD]
    cs = [r for r in rs if r["x"] <= 0.03 and r["corr"][3] <= BUD]
    rb = max(raw, key=lambda r: r["N"]) if raw else None
    cb = max(cs, key=lambda r: r["N"]) if cs else None
    r_s = ("%s, %d (%s)" % (name(rb), 2 * rb["N"], "p=%d" % rb["p"])) if rb else "none <= 4 h"
    c_s = ("%s, %d" % (name(cb), 2 * cb["N"])) if cb else "none <= 4 h"
    # closest-to-budget option for families without any feasible run
    if not rb:
        m = min(rs, key=lambda r: r["raw"][3])
        r_s = "none; best option %s = %d, %.2f h" % (name(m), 2 * m["N"], m["raw"][3])
    print("| %s %s | %d | %s | %s | %s | %s |" % (key[0], key[1], key[2], r_s,
          ("%.2f" % rb["raw"][3]) if rb else "-", c_s, ("%.2f / %.2f" % (cb["raw"][3], cb["corr"][3])) if cb else "-"))

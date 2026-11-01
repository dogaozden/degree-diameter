# distribution summary over many random S (Delta=4): uncovered@10 per side (A, B) and ball ratios
import sys, math, statistics
sys.path.insert(0, "/home/user/degree-diameter/research/squads/beyond11b/r2/h13")
from ball import Frob, SLn, is_prime, run, W
fams = {
 "F761x19": lambda: Frob(761, 19),
 "SL13x7": lambda: SLn(13, 7),
 "SL23": lambda: SLn(23, 1),
 "FROB3": lambda: Frob(next(p for p in range(4800, 5000) if is_prime(p) and p % 3 == 1), 3),
}
name = sys.argv[1]; nseed = int(sys.argv[2])
if name.startswith("F") and "_" in name:
    p_, k_ = map(int, name[1:].split("_")); G = Frob(p_, k_)
else:
    G = fams[name]()
N = G.N; D = 4
unc = []; r8 = []; r10 = []; r6 = []; ty = {"central": [], "other": []}
for sd in range(nseed):
    r = run(G, D, 5000 + sd)
    unc.append(r["A"]["uncov"]["other"] + r["A"]["uncov"]["central"] + r["A"]["uncov"]["id"])
    unc.append(r["B"]["uncov"]["other"] + r["B"]["uncov"]["central"] + r["B"]["uncov"]["id"])
    ty["central"].append(r["A"]["uncov"]["central"]); ty["other"].append(r["A"]["uncov"]["other"])
    for side in ("A",):
        r6.append(r[side]["ball"][6]/ (N*(1-math.exp(-W(D,6)/N))))
        r8.append(r[side]["ball"][8]/ (N*(1-math.exp(-W(D,8)/N))))
        r10.append(r[side]["ball"][10]/ (N*(1-math.exp(-W(D,10)/N))))
mu = N*math.exp(-W(D,10)/N)
print(f"{G.name} N={N} seeds={nseed} model mu10={mu:.1f}")
print(f"  uncov@10 (both sides pooled): min={min(unc)} median={statistics.median(unc)} mean={statistics.mean(unc):.1f} max={max(unc)}")
print(f"  A-side uncov@10 medians: central={statistics.median(ty['central'])} other={statistics.median(ty['other'])}; involution (noncentral)=0 by construction (SL: unique involution -I; Frobenius: odd order)")
print(f"  ball/model ratio A-side: t=6 med {statistics.median(r6):.3f}  t=8 med {statistics.median(r8):.3f} mean {statistics.mean(r8):.3f}  t=10 med {statistics.median(r10):.3f}")

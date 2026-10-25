"""Score many two-pair starts with po7 (SCORE=1). Writes sweep.tsv: cost, file, variant, mode, meet, xsp, seed."""
import subprocess, os, sys, random, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = [sys.argv[0]]
import importlib.util
spec = importlib.util.spec_from_file_location("gen", os.path.join(HERE, "gen.py")); gen = importlib.util.module_from_spec(spec); spec.loader.exec_module(gen)
combos = []
for v in ("a", "b", "c"):
    for mode, meet, xsp in [("spread", 0, 0), ("spread", 1, 0), ("spread", 0, 1), ("random", 0, 0), ("random", 1, 0), ("random", 0, 1), ("absolute", 0, 0), ("absolute", 0, 1)]:
        combos.append((v, mode, meet, xsp))
for v in ("a2", "b2"):
    for mode in ("spread", "random"):
        combos.append((v, mode, 0, 0))
NSEED = int(os.environ.get("NSEED", "30"))
rows = []
for (v, mode, meet, xsp) in combos:
    for seed in range(NSEED):
        rng = random.Random(1000 * seed + 7)
        r = gen.build(v, mode, rng, bool(meet), bool(xsp))
        if r is None: continue
        p = os.path.join(HERE, "starts", f"s_{v}_{mode}_{meet}{xsp}_{seed}.in")
        gen.write(p, *r)
        out = subprocess.run(["./po7", p], env=dict(os.environ, SCORE="1"), capture_output=True, text=True, cwd=HERE).stdout
        m = re.search(r"cost=(\d+)", out)
        c = int(m.group(1)) if m else -1
        rows.append((c, p, v, mode, meet, xsp, seed))
    best = min([r for r in rows if r[2] == v and r[3] == mode and r[4] == meet and r[5] == xsp] or [(-1,)], key=lambda r: r[0] if r[0] >= 0 else 1e9)
    print(v, mode, meet, xsp, "best", best[0], best[1] if len(best) > 1 else "", flush=True)
rows.sort()
with open(os.path.join(HERE, "sweep.tsv"), "w") as f:
    for r in rows: f.write("\t".join(map(str, r)) + "\n")
print("total", len(rows), "min", rows[0][0])
for r in rows[:12]: print(r)

# Summarise c8 runs: E18 = median(evals, unsolved counted as 3x) * exp((18 - mu) / 4.5), per variant.
import glob, math, re, statistics, os
HERE = os.path.dirname(os.path.abspath(__file__))
rows = {}
for f in sorted(glob.glob(os.path.join(HERE, "logs", "*.out"))):
    name = os.path.basename(f)[:-4]                      # e.g. L30_s1
    var, seed = name.rsplit("_s", 1)
    txt = open(f).read()
    m = re.search(r"RESULT .* best=(\d+) evals=(\d+) time=([\d.]+)", txt)
    full = "full diameter check: OK" in txt
    if not m:
        rows.setdefault(var, []).append((int(seed), None, None, None, False)); continue
    best, evals, tm = int(m.group(1)), int(m.group(2)), float(m.group(3))
    rows.setdefault(var, []).append((int(seed), best, evals, tm, full))
mu = 18.25
for f in glob.glob(os.path.join(HERE, "logs", "*.err")):
    m = re.search(r"mu = ([\d.]+)", open(f).read())
    if m: mu = float(m.group(1)); break
print(f"mu = {mu}  factor exp((18-mu)/4.5) = {math.exp((18 - mu) / 4.5):.4f}")
summary = {}
for var in sorted(rows):
    vals = []
    print(f"variant {var}:")
    for seed, best, evals, tm, full in sorted(rows[var]):
        if evals is None:
            print(f"  seed {seed}: no RESULT line"); continue
        solved = best == 0
        vals.append(evals if solved else 3 * evals)
        print(f"  seed {seed}: best={best} evals={evals} time={tm}s solved={solved} full_check_OK={full}")
    if vals:
        med = statistics.median(vals)
        e18 = med * math.exp((18 - mu) / 4.5)
        summary[var] = (med, e18, sum(1 for v in vals if v < 3 * 10**9))
        print(f"  median(evals, unsolved x3) = {med:.0f}  E18 = {e18:.0f}")

# near misses of the r1/c15 (4,13) solution: replace the last generator by random elements, measure holes
import random, subprocess, os, collections
m, k, r = 4903, 19, 230
base = [(0, 0), (1818, 17), (4490, 6), (4768, 7)]
random.seed(11)
rows = []
for trial in range(40):
    x = (random.randrange(m), random.randrange(k))
    while x == (0, 0) or x in base[:3]:
        x = (random.randrange(m), random.randrange(k))
    S = base[:3] + [x]
    env = dict(os.environ, FIXS=" ".join(f"{a},{j}" for a, j in S), LIST="1")
    out = subprocess.run(["./meta_eval", str(m), str(k), str(r), "13", "1", "1"], env=env,
                         capture_output=True, text=True, timeout=100).stdout.splitlines()
    summ = out[-2] if len(out) >= 2 else ""
    holes = [l.split() for l in out if l.startswith("HOLE")]
    cA = collections.Counter(); cB = collections.Counter()
    for h in holes:
        j = int(h[3].split("=")[1]); side = h[1]
        (cA if side == "A" else cB)["j0" if j == 0 else "jne0"] += 1
    cost = sum(1 for _ in holes)
    rows.append((cost, x, dict(cA), dict(cB)))
    print(f"x=({x[0]},{x[1]}) cost={cost} A={dict(cA)} B={dict(cB)}", flush=True)
rows.sort()
import statistics
costs = [r_[0] for r_ in rows]
print("SUMMARY trials=40 min=%d median=%s mean=%.1f max=%d" % (min(costs), statistics.median(costs), statistics.mean(costs), max(costs)))

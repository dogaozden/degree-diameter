"""Summarise CHAIN lines of haar_tw runs: python3 chains.py LOG [LOG ...]  (min per fresh descent, ORBW=3 units)."""
import sys, re, statistics
mins, secs, evals = [], 0.0, 0
for path in sys.argv[1:]:
    for line in open(path, errors="replace"):
        m = re.match(r"CHAIN \d+ min (-?\d+) secs ([\d.]+) evals (\d+)", line)
        if m:
            mins.append(int(m.group(1))); secs += float(m.group(2)); evals += int(m.group(3))
if not mins:
    print("no CHAIN lines"); sys.exit()
n = len(mins)
print("descents %d  cpu-s %.0f  evals %d  (%.0f evals/s)" % (n, secs, evals, evals / max(secs, 1)))
print("min %d  median %s  mean %.1f" % (min(mins), statistics.median(mins), statistics.mean(mins)))
for t in (6, 9, 12, 15):
    c = sum(1 for x in mins if x <= t)
    print("  P(min <= %2d) = %d/%d = %.3f" % (t, c, n, c / n))
hist = {}
for x in mins:
    hist[x] = hist.get(x, 0) + 1
print("hist:", " ".join("%d:%d" % (k, hist[k]) for k in sorted(hist)[:14]))

# A1 follow-up: bulk (cost < 310) and intermediate (310 <= cost < 1e6) classes, degenerate positions across pairings.
import re, statistics
RANDBV = 1000000
TAGS = ["afrob1_ar2", "afrob2_ar2", "afrob3_ar2", "afrob4_ar2", "afrob1_ar6", "afrob1_ar7"]
seqs = {}
for t in TAGS:
    seqs[t] = [int(m.group(2)) for m in re.finditer(r"^SAMPLE (\d+) (-?\d+)$", open("randorb_%s.log" % t).read(), re.M)]
print("tag          n   degen(>=1e6)  inter(310..1e6)  bulk(<310): n  mean   median  sd    min  p10  p25  P(<=30) P(<=40) P(<=60)")
for t in TAGS:
    s = seqs[t]; n = len(s)
    deg = [c for c in s if c >= RANDBV]; inter = [c for c in s if 310 <= c < RANDBV]; bulk = sorted(c for c in s if c < 310)
    q = lambda p: bulk[int(p * (len(bulk) - 1))]
    print("%-12s %3d   %3d (%4.1f%%)    %3d (%4.1f%%)     %3d  %6.2f %6.1f %6.2f %4d %4d %4d    %5.1f%%  %5.1f%%  %5.1f%%" % (
        t, n, len(deg), 100 * len(deg) / n, len(inter), 100 * len(inter) / n, len(bulk),
        statistics.mean(bulk), statistics.median(bulk), statistics.pstdev(bulk), bulk[0], q(0.1), q(0.25),
        100 * sum(c <= 30 for c in s) / n, 100 * sum(c <= 40 for c in s) / n, 100 * sum(c <= 60 for c in s) / n))
print()
print("intermediate costs (310 <= cost < 1e6) by sample index:")
for t in TAGS:
    print("  %-12s" % t, [(i, c) for i, c in enumerate(seqs[t]) if 310 <= c < RANDBV])
print()
print("degenerate sample indices (cost >= 1e6):")
for t in TAGS:
    print("  %-12s" % t, [i for i, c in enumerate(seqs[t]) if c >= RANDBV])
print()
# same-seed comparison on the common prefix (first 40 samples) across the four AR=2 pairings
n40 = 40
print("first 40 samples, cost classes (D = degenerate, I = intermediate, b = bulk) per index:")
for t in TAGS[:4] + ["afrob1_ar6", "afrob1_ar7"]:
    print("  %-12s" % t, "".join("D" if c >= RANDBV else ("I" if c >= 310 else "b") for c in seqs[t][:n40]))
print()
# pairwise agreement of degenerate status and of the exact cost on the first 40 samples
for a in TAGS[:4]:
    row = []
    for b in TAGS[:4]:
        same_deg = sum((seqs[a][i] >= RANDBV) == (seqs[b][i] >= RANDBV) for i in range(n40))
        row.append("%d/40" % same_deg)
    print("  deg-status agreement with %-10s" % a, row)

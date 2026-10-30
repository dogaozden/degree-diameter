#!/usr/bin/env python3
"""Summarise logs/sweep_anti.txt (one line per group of the self-dual Haar sweep): per order, the number of groups
searched, how many had a CAPPED type, and the groups with solutions.  usage: sweep_table.py [logs/sweep_anti.txt]"""
import sys, glob, os, collections
path = sys.argv[1] if len(sys.argv) > 1 else "logs/sweep_anti.txt"
done = {}
for line in open(path):
    t = line.split()
    if len(t) < 12 or t[-4] != "rc" or t[-3] != "0":
        continue
    done[(int(t[0]), int(t[1]))] = int(t[t.index("sols") + 1])
by = collections.defaultdict(lambda: [0, 0, []])
for (n, i), s in sorted(done.items()):
    f = f"logs/exh/{n}_{i}_anti.out"
    capped = os.path.exists(f) and any(l.startswith("ANTI ") and "CAPPED" in l and (" f 1 " in l or " f 3 " in l) for l in open(f))
    by[n][0] += 1
    by[n][1] += capped
    if s:
        by[n][2].append(f"{i} ({s})")
print("| order | vertices | groups searched | (1,3)/(3,2) capped | groups with solutions |")
print("|---:|---:|---:|---:|---|")
for n in sorted(by):
    g, c, h = by[n]
    print(f"| {n} | {2 * n} | {g} | {c} | {', '.join(h) if h else '-'} |")
print(f"\ntotal groups: {len(done)}, with solutions: {sum(1 for v in done.values() if v)}")

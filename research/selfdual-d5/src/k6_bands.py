#!/usr/bin/env python3
"""k6_bands.py: K = 6 sweep coverage by order band and number of involutions: searched / listed (smallest near miss)."""
import collections
inv = {}
for l in open("logs/groups_343_450.txt"):
    t = l.split(); inv[(int(t[0]), int(t[1]))] = int(t[3])
res = {}
for l in open("logs/K6/sweep.txt"):
    t = l.split()
    if len(t) > 4 and t[0].isdigit() and "rc" in t and t[t.index("rc") + 1] == "0":
        b = t[t.index("best") + 1]; res[(int(t[0]), int(t[1]))] = int(b) if b != "NA" else 1 << 40
band = lambda n: "343-360" if n <= 360 else "361-400" if n <= 400 else "401-450"
ib = lambda i: "<= 1" if i <= 1 else "3-7" if i <= 7 else "8-31" if i <= 31 else "> 31"
c = collections.defaultdict(lambda: [0, 0, 1 << 40])
for k, i in inv.items():
    e = c[(band(k[0]), ib(i))]; e[1] += 1
    if k in res: e[0] += 1; e[2] = min(e[2], res[k])
print("| orders (vertices) | inv <= 1 | inv 3-7 | inv 8-31 | inv > 31 |"); print("|---|---:|---:|---:|---:|")
for b, v in [("343-360", "686-720"), ("361-400", "722-800"), ("401-450", "802-900")]:
    row = []
    for i in ["<= 1", "3-7", "8-31", "> 31"]:
        s, t, bb = c[(b, i)]; row.append(f"{s} / {t}" + (f" (best {bb})" if s and bb < 1 << 40 else ""))
    print(f"| {b} ({v}) | " + " | ".join(row) + " |")

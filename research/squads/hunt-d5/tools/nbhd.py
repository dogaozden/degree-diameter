#!/usr/bin/env python3
"""Exact r-swap neighbourhood of a Haar set S (hunt-d5): nbhd.py TABLE d "s0 s1 ..." r [LIMIT]
For every core = {s0} + (d-1-r) other elements of S, runs `haar5 complete` (all completions by r new elements).
s0 should be the identity 0 (translate S first). Prints each core's minimum and any set with cost <= LIMIT."""
import itertools, subprocess, sys, os
tab, d, S, r = sys.argv[1], sys.argv[2], list(map(int, sys.argv[3].split())), int(sys.argv[4])
lim = sys.argv[5] if len(sys.argv) > 5 else "0"
h5 = os.path.join(os.path.dirname(os.path.abspath(__file__)), "haar5")
best = None
for core in itertools.combinations(S[1:], len(S) - 1 - r):
    c = [S[0]] + list(core)
    out = subprocess.run([h5, "complete", tab, d, " ".join(map(str, c)), lim], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if line.startswith("cost"): print(line, flush=True)
        if line.startswith("RESULT"):
            mn = int(line.split("min=")[1].split()[0]); best = mn if best is None else min(best, mn)
            print("core", c, line.split("RESULT complete ")[1], flush=True)
print("NBHD best", best)

#!/usr/bin/env python3
"""Summarize a squad round from the haar_big0 logs in its card folders: per log, group, orbit, mu, best cost, evals,
solved or not.  usage: roundsum.py ROUND_DIR"""
import sys, os, re, glob
for card in sorted(glob.glob(os.path.join(sys.argv[1], "*/"))):
    rows = []
    for lg in sorted(glob.glob(os.path.join(card, "**", "*.log"), recursive=True)):
        txt = open(lg, errors="ignore").read()
        g = re.search(r"group (\w+ \d+) x Z_(\d+)", txt); o = re.search(r"ORBIT k=(\d+) m=(\d+) f=(\d+)", txt)
        mu = re.search(r"mu=([\d.]+)", txt)
        if not g or not o or "RANDORB d=" in txt: continue
        bests = [int(x) for x in re.findall(r"best=(\d+)", txt)]; ev = re.findall(r"evals=(\d+)", txt)
        solved = re.search(r"RESULT .*best=0 ", txt) is not None
        rows.append(f"{g[1]} x{g[2]} k{o[1]}m{o[2]}f{o[3]} mu{float(mu[1]):.1f} best={min(bests) if bests else '?'} evals={ev[-1] if ev else '?'}{' SOLVED' if solved else ''}")
    print(os.path.basename(card.rstrip('/')), " | ".join(rows) if rows else "(no search log)")

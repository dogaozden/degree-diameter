#!/usr/bin/env python3
"""Card c3: collect the good states of prod psl 7 sl 8 7 from the checkpoints and CHAIN lines of the main runs.

Writes next to this script:
  states.json  one entry per distinct set: id, S (10 element indices, S[0] = e, orbits at positions 1-3, 4-6, 7-9),
               stated (costs printed by the runs for this set), src (where it came from)
  parents.txt  the same sets, one per line, in states.json order (input of the EVALS run)
"""
import glob
import json
import os
import re

RUNS = "/home/user/degree-diameter/research/d10D8/runs"
HERE = os.path.dirname(os.path.abspath(__file__))
PAT = "d10D8_prod_psl_7_sl_8_7_"

records = []  # (source file, kind, stated cost, S)
n_nos = 0     # CHAIN lines without a set
for f in sorted(glob.glob(os.path.join(RUNS, PAT + "*.ckpt"))):
    with open(f) as h:
        lines = h.read().splitlines()
    if len(lines) < 2:
        continue
    m = re.search(r"best=(\d+)", lines[0])
    S = [int(x) for x in lines[1].split()]
    if not m or len(S) != 10:
        continue
    records.append((os.path.basename(f), "ckpt", int(m.group(1)), S))

for f in sorted(glob.glob(os.path.join(RUNS, PAT + "*.log"))):
    with open(f) as h:
        for line in h:
            if not line.startswith("CHAIN "):
                continue
            t = line.split()
            if "S" not in t:   # older CHAIN lines carry no set (8 fields): no state to use
                n_nos += 1
                continue
            S = [int(x) for x in t[t.index("S") + 1:]]
            if len(S) != 10:
                continue
            records.append((os.path.basename(f), "chain", int(t[t.index("min") + 1]), S))

e_vals = {S[0] for _, _, _, S in records}
assert len(e_vals) == 1, e_vals  # position 0 is e in every record
E = e_vals.pop()

by_set = {}
for src, kind, stated, S in records:
    if len(set(S)) != 10:
        print("skipping a record with a repeated element:", src, kind)
        continue
    st = by_set.setdefault(frozenset(S), {"S": S, "src": [], "stated": []})
    st["src"].append(src + ":" + kind)
    st["stated"].append(stated)

states = sorted(by_set.values(), key=lambda st: (min(st["stated"]), st["src"][0]))
for i, st in enumerate(states):
    st["id"] = "s%03d" % i

with open(os.path.join(HERE, "states.json"), "w") as h:
    json.dump(states, h, indent=1)
with open(os.path.join(HERE, "parents.txt"), "w") as h:
    for st in states:
        h.write(" ".join(map(str, st["S"])) + "\n")

n_ckpt = sum(1 for r in records if r[1] == "ckpt")
n_chain = sum(1 for r in records if r[1] == "chain")
print(f"e index = {E}; records: {n_ckpt} checkpoint, {n_chain} CHAIN lines with a set ({n_nos} CHAIN lines without a set); "
      f"distinct sets: {len(states)}")
print("stated minima of the distinct sets (lowest 15):", [min(st["stated"]) for st in states[:15]])

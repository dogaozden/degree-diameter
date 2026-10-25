#!/usr/bin/env python3
"""Card c3: summary of the crossover evaluation (parents_cost.txt and cross_cost.txt are EVALS outputs)."""
import json
import os
import statistics

HERE = os.path.dirname(os.path.abspath(__file__))
states = json.load(open(os.path.join(HERE, "states.json")))
sets = [list(map(int, l.split())) for l in open(os.path.join(HERE, "cross_sets.txt")) if l.strip()]
meta = json.load(open(os.path.join(HERE, "cross_meta.json")))
pcost = [int(x) for x in open(os.path.join(HERE, "parents_cost.txt")).read().split()]
ccost = [int(x) for x in open(os.path.join(HERE, "cross_cost.txt")).read().split()]
assert len(pcost) == len(states) and len(ccost) == len(sets) == len(meta)

pc = {st["id"]: c for st, c in zip(states, pcost)}
bad = [st["id"] for st, c in zip(states, pcost) if any(v != c for v in st["stated"])]
print("evaluator vs stated checkpoint/CHAIN costs: mismatches", len(bad), bad)
best_parent = min(pcost)
print("parents:", len(states), "distinct good states; costs sorted:", sorted(pcost))
print("best parent cost:", best_parent, "(states:", [st["id"] for st, c in zip(states, pcost) if c == best_parent], ")")

n = len(ccost)
srt = sorted(ccost)
print(f"crossovers evaluated: {n}")
print(f"best crossover cost: {srt[0]} (count at best: {srt.count(srt[0])})")
print(f"below 20: {sum(c < 20 for c in ccost)}   below 12: {sum(c < 12 for c in ccost)}   cost 0: {sum(c == 0 for c in ccost)}")
print("quantiles p1 p10 p50 p90: ", srt[n // 100], srt[n // 10], srt[n // 2], srt[9 * n // 10])
print("lowest 15 crossover costs:", srt[:15])
better = sum(c < min(pc[m["A"]], pc[m["B"]]) for c, m in zip(ccost, meta))
print(f"crossovers strictly below the better of their two parents: {better}")
print(f"crossovers at or below the best parent ({best_parent}): {sum(c <= best_parent for c in ccost)}")

order = sorted(range(n), key=lambda i: ccost[i])
print("top 8 crossovers (cost, A, B, A orbits kept, B orbit, parents' costs):")
for i in order[:8]:
    m = meta[i]
    print("  ", ccost[i], m["A"], m["B"], m["A_orbits"], m["B_orbit"], pc[m["A"]], pc[m["B"]])

if 0 in ccost:
    zs = [sets[i] for i in range(n) if ccost[i] == 0]
    with open(os.path.join(HERE, "zero_cost_sets.txt"), "w") as h:
        for z in zs:
            h.write(" ".join(map(str, z)) + "\n")
    print("ZERO-COST CROSSOVER SETS SAVED:", len(zs))

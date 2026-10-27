#!/usr/bin/env python3
"""Card c3: crossovers of good states of prod psl 7 sl 8 7.

For every ordered pair of distinct states (A, B) and every choice of 2 of A's 3 orbits (positions 1-3, 4-6, 7-9) and
1 of B's 3 orbits, the set {e} + O_a + O_b + O'_c is a candidate (9 per pair; sets with a repeated element are skipped).
Writes cross_sets.txt (one set per line, position 0 = e) and cross_meta.json (A id, B id, pair of A orbits, B orbit).
"""
import itertools
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
states = json.load(open(os.path.join(HERE, "states.json")))
E = states[0]["S"][0]
assert all(st["S"][0] == E for st in states)


def orbits(S):
    return [S[1 + 3 * j: 4 + 3 * j] for j in range(3)]


lines, meta, skipped = [], [], 0
for A in states:
    OA = orbits(A["S"])
    for B in states:
        if A["id"] == B["id"]:
            continue
        OB = orbits(B["S"])
        for pa in itertools.combinations(range(3), 2):
            for c in range(3):
                els = [E] + OA[pa[0]] + OA[pa[1]] + OB[c]
                if len(set(els)) != 10:
                    skipped += 1
                    continue
                lines.append(" ".join(map(str, els)))
                meta.append({"A": A["id"], "B": B["id"], "A_orbits": list(pa), "B_orbit": c})

with open(os.path.join(HERE, "cross_sets.txt"), "w") as h:
    h.write("\n".join(lines) + "\n")
with open(os.path.join(HERE, "cross_meta.json"), "w") as h:
    json.dump(meta, h)
print(f"states {len(states)}; ordered pairs {len(states) * (len(states) - 1)}; crossover sets {len(lines)}; "
      f"skipped (repeated element) {skipped}")

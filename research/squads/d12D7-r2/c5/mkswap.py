# c5 helper: turn a chosen set of hub neighbours of 664300 into an edit list (2-switches keep every degree <= 12).
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d12D7-r2/c5")
from hubdata import *
def build(hid, owner0, chosen_ids, out, donor_pick=0, log=False):
    HL, HP, oL, oP, E = load()
    aL, aP = adjacency(HL, HP, E)
    j = hid - 664300
    old = [678700 + k for k in aL[j]]
    ops = ["- %d %d" % (hid, owner0)]
    keep = [g for g in chosen_ids if g in old]
    drop = [g for g in old if g not in chosen_ids]
    new = [g for g in chosen_ids if g not in old]
    assert len(new) == len(drop) + 1, (len(new), len(drop))
    donors = []
    for g in new:
        k = g - 678700
        cands = [664300 + x for x in aP[k] if 664300 + x != hid]
        x = cands[donor_pick % len(cands)]
        donors.append((g, x))
    for i, d in enumerate(drop):
        g, x = donors[i]
        ops += ["- %d %d" % (hid, d), "- %d %d" % (g, x), "+ %d %d" % (x, d), "+ %d %d" % (hid, g)]
    for g, x in donors[len(drop):]:
        ops += ["- %d %d" % (g, x), "+ %d %d" % (hid, g)]
    open(out, "w").write("\n".join(ops) + "\n")
    return keep, drop, new, donors
if __name__ == "__main__":
    hid = int(sys.argv[1]); owner0 = int(sys.argv[2]); out = sys.argv[3]
    chosen = [678700 + int(c) for c in sys.argv[4].split(",")]
    dp = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    keep, drop, new, donors = build(hid, owner0, chosen, out, dp)
    print("kept old:", keep, "dropped old:", drop, "new:", new, "donors:", donors)

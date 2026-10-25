# c5: real-graph hill climb over the 8 hub neighbours of 664300 (level-0 owner removed); donors chosen by search.
import sys, time, json
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d12D7-r2/c5")
from driver import *
cov = np.fromfile(D_ + "covA.cov", dtype=np.uint64).reshape(14400, -1)
ev = Eval()
TLIM = float(sys.argv[1]) if len(sys.argv) > 1 else 400
chosen = [678700 + c for c in [6195, 14028, 6277, 2741, 6704, 9694, 11888, 4692]]
donors = {}
for g in chosen:
    if g not in ev.old: donors[g] = donors_options(g)[0]
order = [g for g in chosen if g not in ev.old]
def score(ch, dn, od):
    return ev.eval_scen(ev.plan(ch, dn, od))
# start from the donor-optimised state found earlier
donors = {684895: 671200, 692728: 671429, 684977: 676442, 681441: 667041, 685404: 668078, 688394: 664459, 690588: 664656, 683392: 665260}
order = [684895, 692728, 684977, 681441, 685404, 688394, 690588, 683392]
best = score(chosen, donors, order)
print("start", best, flush=True)
t0 = time.time()
def shortlist(ch, slot_g, top=120):
    others = [c - 678700 for c in ch if c != slot_g]
    O = np.zeros(cov.shape[1], dtype=np.uint64)
    for c in others: O |= cov[c]
    gain = np.bitwise_count(cov & ~O).sum(axis=1).astype(np.int64)
    gain[[c for c in others]] = -1
    idx = np.argsort(-gain)[:top]
    return [678700 + int(i) for i in idx]
rnd = 0
while time.time() - t0 < TLIM:
    rnd += 1
    improved = False
    for slot in list(chosen):
        sl = shortlist(chosen, slot)
        for c in sl:
            if c in chosen: continue
            ch2 = [c if g == slot else g for g in chosen]
            dn2 = dict(donors); od2 = list(order)
            if slot in dn2: del dn2[slot]
            if slot in od2: od2.remove(slot)
            # donor options for the newcomer (only if not an old neighbour of 664300)
            if c in ev.old:
                cand_dn = [None]
            else:
                cand_dn = donors_options(c)[:3]
            for x in cand_dn:
                if x is not None: dn2[c] = x
                od3 = od2 + ([c] if c not in ev.old else [])
                # dropped old hubs are matched in order; keep order consistent
                m = score(ch2, dn2, od3)
                if m < best:
                    best = m; chosen = ch2; donors = dict(dn2); order = list(od3)
                    improved = True
                    print("round", rnd, "slot", slot - 678700, "-> cand", c - 678700, "donor", x, "misses", best, "t", round(time.time() - t0), flush=True)
                    break
            if time.time() - t0 > TLIM: break
            if improved: break
        if improved or time.time() - t0 > TLIM: break
    if not improved:
        print("round", rnd, "no improving replacement, best", best, flush=True)
        if time.time() - t0 > TLIM: break
print("FINAL", best, json.dumps({"chosen_idx": [c - 678700 for c in chosen], "donors": {str(k): v for k, v in donors.items()}, "order": order}), flush=True)

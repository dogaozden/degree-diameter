# c5 driver: rewire hub 664300 (level-0 owner removed) and evaluate misses in the real graph via hubbatch.
import subprocess, sys, random
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d12D7-r2/c5")
from hubdata import *
D_ = "/home/user/degree-diameter/research/squads/d12D7-r2/c5/"
HL, HP, oL, oP, E = load()
aL, aP = adjacency(HL, HP, E)
HID = 664300; OWN0 = 6524
class Eval:
    def __init__(self, hid=HID, src_owner0=OWN0, edges=D_ + "g.edges", D=7):
        self.p = subprocess.Popen([D_ + "hubbatch", edges, str(hid), str(D)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.hid = hid; self.own0 = src_owner0
        self.old = [678700 + k for k in aL[hid - 664300]]
    def eval_scen(self, ops):
        self.p.stdin.write("\n".join(ops) + "\n=\n"); self.p.stdin.flush()
        return int(self.p.stdout.readline().split()[0])
    def plan(self, chosen, donors, pairing=None):
        """chosen: point-side hub ids (the new neighbour set of hub). donors: dict new g -> line-side hub id x.
        Dropped old neighbours are matched to the new hubs that have donors, in the order of pairing (list of g)."""
        hid = self.hid
        keep = [g for g in chosen if g in self.old]
        drop = [g for g in self.old if g not in chosen]
        new = [g for g in chosen if g not in self.old]
        ops = ["- %d %d" % (hid, self.own0)]
        order = pairing if pairing is not None else new
        for i, d in enumerate(drop):
            g = order[i]; x = donors[g]
            ops += ["- %d %d" % (hid, d), "- %d %d" % (g, x), "+ %d %d" % (x, d), "+ %d %d" % (hid, g)]
        for g in order[len(drop):]:
            x = donors[g]; ops += ["- %d %d" % (g, x), "+ %d %d" % (hid, g)]
        return ops
def donors_options(g):
    return [664300 + x for x in aP[g - 678700] if 664300 + x != HID]

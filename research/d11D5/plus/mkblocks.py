"""Blocks for block-constrained sigma moves: for each i, the old points of L_i (incl. p_i) and the points of delta(p_i)."""
import json, sys, os
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5"); here = os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n, L, d_pt, d_ln, inv = load(8); os.chdir(here)
d = json.load(open(sys.argv[1])); lines, pts = d["lines"], d["pts"]
with open(sys.argv[2], "w") as g:
    for li, p in zip(lines, pts):
        g.write("9 " + " ".join(map(str, L[li])) + "\n")
        g.write("9 " + " ".join(map(str, L[d_pt[p]])) + "\n")

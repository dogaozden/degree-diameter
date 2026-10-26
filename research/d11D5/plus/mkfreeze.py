import json, sys
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
import os; here = os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n, L, d_pt, d_ln, inv = load(8); os.chdir(here)
d = json.load(open(sys.argv[1])); lines, pts = d["lines"], d["pts"]
fr = set()
for li, p in zip(lines, pts):
    fr.add(p)
    fr.update(q for q in L[li] if q != p)          # z in L_i \ p_i
    for m in range(n):
        if p in L[m]: fr.add(d_ln[m])               # delta(m) for lines m through p_i (incl. L_i)
open(sys.argv[2], "w").write("\n".join(map(str, sorted(fr))) + "\n")
print("frozen", len(fr))

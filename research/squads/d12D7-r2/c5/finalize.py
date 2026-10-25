# c5: rebuild the ops of the best real-graph configuration from the climb's FINAL line, write g3.edges.
import sys, json
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d12D7-r2/c5")
from driver import *
line = [l for l in open(sys.argv[1]) if l.startswith("FINAL")][-1]
best = int(line.split()[1]); js = json.loads(line[len("FINAL %d " % best):])
chosen = [678700 + c for c in js["chosen_idx"]]
donors = {int(k): v for k, v in js["donors"].items()}
order = js["order"]
ev = Eval()
ops = ev.plan(chosen, donors, order)
open("ops_final.txt", "w").write("\n".join(ops) + "\n")
print("best", best, "ops", len(ops))
print("chosen", chosen)
print("donors", donors)
print("order", order)

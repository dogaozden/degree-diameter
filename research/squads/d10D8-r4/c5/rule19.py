import sys, subprocess, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from rule18 import build, q, N
m, sh, iota, ma, mb = 19, 121, [0, 2, 7, 5], 9, 4
sigs, mvs, hv = build(m, sh, iota, ma, mb)
sol = os.path.join(HERE, "sols", "explicit_q3_m%d.sol" % m)
write_sol(sol, q, m, sigs, mvs, hv)
r = subprocess.run(["timeout", "120", "nice", "-n", "19", "./verify", "hex/hex_q3.bin", sol, "8"], cwd=HERE, capture_output=True, text=True)
print("verify.c (independent BFS):", r.stdout.strip() or r.stderr.strip())
print("lift3 fullcost:", evaluate(q, m, sigs, mvs, hv, tag="explicit19"))
print("solution file:", sol)

import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/own-small/r1/a1/work")
from common import *
from rq import *
k, E0 = base_edges("/home/user/degree-diameter/research/squads/own-small/tools/bases/cubic/b22_cubic.txt")
lines = [l for l in open("/home/user/degree-diameter/research/squads/own-small/seeds/g220_2_cost2.volts") if ":" in l]
print("n lines", len(lines))
# G-lift itself (flift convention volts = the file)
for li in [0]:
    volts = list(map(int, lines[li].split(":")[1].split()))
    n, out = lift_edges(k, N, M, E0, volts)
    write_edges("/home/user/degree-diameter/research/squads/own-small/r1/a1/work/check_G_l0.edges", n, out)
    print(n, len(out))

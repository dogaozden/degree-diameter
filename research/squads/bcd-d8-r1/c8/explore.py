import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
N = H.N
print("N", N, "KA", H.KA, "point orbits", len(H.prep), "line orbits", len(H.lrep))
# check: points on each line in distinct point orbits?
bad = 0
for l in range(N):
    os_ = [H.porb[p] for p in H.lines[l]]
    if len(set(os_)) < len(os_): bad += 1
print("lines with two points in same point-orbit:", bad)
# check each line-orbit rep
badrep = sum(1 for l in H.lrep if len(set(H.porb[p] for p in H.lines[l])) < len(H.lines[l]))
print("line-orbit reps with repeated point orbit:", badrep)

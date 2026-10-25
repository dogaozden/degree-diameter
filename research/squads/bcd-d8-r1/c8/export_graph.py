import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin')
N = H.N
# collinearity graph: adjacency list (30 per point), written as text: N then rows
with open('/home/user/degree-diameter/research/squads/bcd-d8-r1/c8/coll.txt', 'w') as f:
    f.write(f"{N}\n")
    for p in range(N):
        nb = set()
        for L in H.plines[p]:
            for x in H.lines[L]:
                if x != p: nb.add(int(x))
        assert len(nb) == 30
        f.write(" ".join(map(str, sorted(nb))) + "\n")
print("ok")

import sys
coords_path = "/home/user/degree-diameter/research/cell147/data/coords13.txt"
flags_path = "/home/user/degree-diameter/research/cell147/units/sols/flags_q13_spread205.txt"
q = 13; C = 11
X = []
with open(coords_path) as f:
    for line in f:
        X.append(tuple(int(v) for v in line.split()))
inE = lambda p: (X[p][4] + C * X[p][0]) % q == 0
flags = [tuple(int(v) for v in l.split()) for l in open(flags_path) if l.strip()]
pts = [p for p, l in flags]
nE = sum(1 for p in pts if inE(p))
lineInE = 0
for p, l in flags:
    pass
print("flags", len(flags), "distinct points", len(set(pts)), "points in E", nE, "points outside E", len(flags) - nE)
print("distinct lines", len(set(l for p, l in flags)))

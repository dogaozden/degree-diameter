import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
q = int(sys.argv[1]); m = int(sys.argv[2])
H = load_hex(q); N = H["N"]
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
# Z10 lemma: hexagon 0, matching 1 raises level by 1, matching 2 by 4 (point -> line)
mv1 = [1 % m] * N; mv2 = [4 % m] * N
hv = [0] * (N * H["Q1"])
print("q", q, "m", m, "lemma-style fullcost", evaluate(q, m, [sig1, sig2], [mv1, mv2], hv, tag="lemma"))

import sys, random, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
q = 3; H = load_hex(q); N = H["N"]; Q1 = H["Q1"]; pl = H["pl"]
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def ev(m, mv1, mv2, hv, tag):
    t = time.time(); c = evaluate(q, m, [sig1, sig2], [mv1, mv2], hv, tag=tag)
    print(tag, "m", m, "fullcost", c, "%.2fs" % (time.time() - t), flush=True); return c
m = 20
ev(m, [1] * N, [4] * N, [0] * (N * Q1), "E1_lemma20")
random.seed(1)
ev(m, [random.randrange(m) for _ in range(N)], [random.randrange(m) for _ in range(N)],
   [random.randrange(m) for _ in range(N * Q1)], "E2_rand20")
ev(16, [random.randrange(16) for _ in range(N)], [random.randrange(16) for _ in range(N)],
   [random.randrange(16) for _ in range(N * Q1)], "E2_rand16")
# r2-style index product rule with c=m: hexagon voltage 6*p*l mod m, mv1=1, mv2=6
pl_ = pl
hv = [(6 * pl[l * Q1 + k] * l) % m for l in range(N) for k in range(Q1)]
ev(m, [1] * N, [6 % m] * N, hv, "E3_idxprod20")

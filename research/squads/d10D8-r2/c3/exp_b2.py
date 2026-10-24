"""Exp B2: test the hexagon-zero candidates that passed at q=2 (a = 1) at q = 3 and q = 4."""
import time, mk
cands = [(11,1,2),(11,1,3),(11,1,4),(11,1,5),(12,1,3),(12,1,4),(12,1,5),(12,1,7),(13,1,3),(13,1,4),(13,1,5),
         (14,1,3),(14,1,4),(14,1,5),(15,1,3),(15,1,4),(16,1,3),(16,1,4),(16,1,5)]
data = {}
for q in (3, 4):
    data[q] = mk.load_hex(q)
for (c, a, b) in cands:
    res = []
    for q in (3, 4):
        N, Q1, pl, co = data[q]
        sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
        hv = [0] * (N * Q1)
        path = "%s/B2_q%d_c%d_%d_%d.sol" % (mk.OUTDIR, q, c, a, b)
        mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
        res.append(mk.evaluate(q, path, "cyc %d" % c))
    print("c=%d mu=(%d,%d): fullcost q3=%s q4=%s" % (c, a, b, res[0], res[1]), flush=True)

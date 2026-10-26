"""Exp C (diagnostic, not explicit): random hexagon voltages (seeded) with constant matching voltages (1,4) or (1,5),
explicit matchings (identity, shift N//3). Shows how much hexagon nonzero voltage helps at q = 4."""
import random, time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
for (c, a, b) in [(12, 1, 4), (13, 1, 5), (16, 1, 4), (20, 1, 4)]:
    out = []
    for seed in (1, 2):
        rnd = random.Random(seed)
        hv = [rnd.randrange(c) for _ in range(N * Q1)]
        path = "%s/C_q%d_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, c, a, b, seed)
        mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
        out.append(mk.evaluate(q, path, "cyc %d" % c))
    print("random hex voltages, c=%d mu=(%d,%d): fullcost seeds 1,2 = %s" % (c, a, b, out), flush=True)

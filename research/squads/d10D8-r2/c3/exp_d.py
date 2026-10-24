"""Exp D (diagnostic): group Z_r x Z_5 (GROUP="prod r 5", element index = 5i + j). Matchings: constant voltages
(0,1) and (0,2), i.e. Z_5 shifts 1 and 2, explicit matchings (identity, shift N//3). Hexagon voltages random in
the Z_r factor {5i} (seeded, NOT explicit: a sanity check that the Z_r x Z_5 structure is viable at q = 4)."""
import random, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
for r in (2, 3, 4, 5):
    c = 5 * r; out = []
    for seed in (1, 2):
        rnd = random.Random(seed)
        hv = [5 * rnd.randrange(r) for _ in range(N * Q1)]
        path = "%s/D_q%d_prod%d5_s%d.sol" % (mk.OUTDIR, q, r, seed)
        mk.write_sol(path, q, 2, c, "prod %d 5" % r, [sig1, sig2], [[1] * N, [2] * N], hv)
        out.append(mk.evaluate(q, path, "prod %d 5" % r))
    print("prod %d 5 (c=%d), random Z_%d hex voltages, mu=(0,1),(0,2): fullcost seeds 1,2 = %s" % (r, c, r, out), flush=True)

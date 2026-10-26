"""Exp A: lemma baseline (hexagon voltages 0, matching voltages 1 and 4 on Z10) with explicit matchings:
sigma1 = identity numbering, sigma2 = numbering shifted by N//3. Checks q = 2, 3, 4 with lift3."""
import sys, time, mk
c, a, b = 10, 1, 4
for q in (2, 3, 4):
    N, Q1, pl, co = mk.load_hex(q)
    sig1 = list(range(N))
    sig2 = [(p + N // 3) % N for p in range(N)]
    hv = [0] * (N * Q1)
    path = "%s/A_q%d_c%d_%d_%d.sol" % (mk.OUTDIR, q, c, a, b)
    mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
    t = time.time(); F = mk.evaluate(q, path, "cyc %d" % c)
    print("q=%d c=%d mu=(%d,%d) explicit sigma: fullcost=%s  (%.1fs wall)" % (q, c, a, b, F, time.time() - t), flush=True)

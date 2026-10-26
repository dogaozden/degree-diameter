"""Exp B: hexagon voltages 0, cyclic Z_c, constant matching voltages (a, b), explicit matchings
(sigma1 = identity numbering, sigma2 = shift by N//3). Scan c = 11..16 at q = 2 (a <= c/2, all b).
Prints the passing (c, a, b) triples."""
import time, mk
q = 2
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
hv = [0] * (N * Q1)
t0 = time.time(); passing = []
for c in range(11, 17):
    for a in range(1, c // 2 + 1):
        for b in range(1, c):
            path = "%s/B_q%d_c%d_%d_%d.sol" % (mk.OUTDIR, q, c, a, b)
            mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
            F = mk.evaluate(q, path, "cyc %d" % c)
            if F == 0: passing.append((c, a, b))
print("q=2 passing (c,a,b):", passing, "time %.1fs" % (time.time() - t0), flush=True)

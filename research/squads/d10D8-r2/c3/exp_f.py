"""Exp F: product rule nu(p -> l) = (p * l) mod c (p, l = point / line index in the hexgen2 numbering), matchings
sigma1 = identity, sigma2 = shift N//3, constant matching voltages (1, b). q = 4. Scan c = 14..20 and several b."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexprod(c):
    hv = [0] * (N * Q1)
    for l in range(N):
        for k in range(Q1):
            hv[l * Q1 + k] = (pl[l * Q1 + k] * l) % c
    return hv
t0 = time.time()
cands = [(14, 1, 4), (14, 1, 5), (14, 1, 3), (15, 1, 4), (15, 1, 5), (16, 1, 4), (16, 1, 5), (16, 1, 3), (16, 1, 6),
         (20, 1, 4), (20, 1, 5), (20, 1, 6), (20, 1, 3), (20, 1, 7)]
for (c, a, b) in cands:
    path = "%s/F_q%d_prod_c%d_%d_%d.sol" % (mk.OUTDIR, q, c, a, b)
    mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hexprod(c))
    F = mk.evaluate(q, path, "cyc %d" % c)
    print("product rule c=%d mu=(%d,%d): fullcost q4=%s" % (c, a, b, F), flush=True)
print("time %.1fs" % (time.time() - t0))

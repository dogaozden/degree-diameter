"""Exp E: explicit hexagon-voltage rules on cyclic Z_c, constant matchings (1,b), explicit matchings
(sigma1 = identity numbering, sigma2 = shift N//3). Flag (p, l) with k = position of p on l (0..q, numbering order)
and its point/line indices. Rules (all non-separable, so not gauge-trivial):
  marking : voltage s on the flag k = 0 of every line (first point of l), 0 elsewhere      (s in Z_c)
  position: voltage s * k                                                                  (s in Z_c)
  product : voltage (s * (p * l)) mod c with p, l the indices of the point and the line     (s in Z_c)
Stops nothing; prints fullcost per (rule, c, mu, s)."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexv(rule, s, c):
    hv = [0] * (N * Q1)
    for l in range(N):
        for k in range(Q1):
            p = pl[l * Q1 + k]
            if rule == "marking": v = s if k == 0 else 0
            elif rule == "position": v = s * k
            elif rule == "product": v = (s * (p * l)) % c if True else 0
            hv[l * Q1 + k] = v % c
    return hv
t0 = time.time()
for (c, a, b, rules) in [(12, 1, 4, ["marking", "position", "product"]), (13, 1, 5, ["marking", "position", "product"])]:
    for rule in rules:
        res = []
        for s in range(1, c):
            path = "%s/E_q%d_%s_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, rule, c, a, b, s)
            mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hexv(rule, s, c))
            res.append((s, mk.evaluate(q, path, "cyc %d" % c)))
        best = min(res, key=lambda x: (x[1] is None, x[1]))
        print("c=%d mu=(%d,%d) %-8s best s=%d fullcost=%s | all: %s" % (c, a, b, rule, best[0], best[1],
              " ".join(str(x[1]) for x in res)), flush=True)
print("time %.1fs" % (time.time() - t0))

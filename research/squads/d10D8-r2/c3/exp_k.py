"""Exp K: product rule nu = s*p*l mod c at q = 4 for c = 17, 18, 19, 20 (matchings identity / shift N//3,
constant (1, b)); scan s, stop at the first DIAMETER_OK. Budget-limited scan (CPU rules)."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexprod(s, c): return [(s * pl[l * Q1 + k] * l) % c for l in range(N) for k in range(Q1)]
t0 = time.time()
plan = [(17, 1, 6), (18, 1, 6), (19, 1, 6), (20, 1, 6), (20, 1, 4)]
for c, a, b in plan:
    found = None; trace = []
    for s in range(1, c):
        path = "%s/K_q%d_product_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, c, a, b, s)
        mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hexprod(s, c))
        F = mk.evaluate(q, path, "cyc %d" % c); trace.append((s, F))
        if F == 0: found = s; break
    best = min((x for x in trace if x[1] is not None), key=lambda x: x[1])
    print("product c=%d mu=(%d,%d): first DIAMETER_OK s=%s, min misses %s, runs %d" % (c, a, b, found, best, len(trace)), flush=True)
print("time %.1fs" % (time.time() - t0))

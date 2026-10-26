"""Exp H: push to c = 15 and 16 at q = 4 with the explicit position rule nu = s*k mod c and the product rule
nu = s*p*l mod c. Matchings identity / shift N//3; constant matching voltages (1, b). Early stop per (rule, c, mu)."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexpos(s, c):
    return [(s * (k % Q1)) % c for l in range(N) for k in range(Q1)]
def hexprod(s, c):
    return [(s * pl[l * Q1 + k] * l) % c for l in range(N) for k in range(Q1)]
t0 = time.time()
plan = [("position", 15, [(1, 3), (1, 6)]), ("product", 15, [(1, 3)]), ("position", 16, [(1, 3), (1, 6)])]
for rule, c, mus in plan:
    for (a, b) in mus:
        found = None; trace = []
        for s in range(1, c):
            hv = hexpos(s, c) if rule == "position" else hexprod(s, c)
            path = "%s/H_q%d_%s_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, rule, c, a, b, s)
            mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
            F = mk.evaluate(q, path, "cyc %d" % c); trace.append((s, F))
            if F == 0: found = s; break
        print("%s c=%d mu=(%d,%d): first DIAMETER_OK s=%s | min misses %s" % (rule, c, a, b, found,
              min((x for x in trace if x[1] is not None), key=lambda x: x[1])), flush=True)
print("time %.1fs" % (time.time() - t0))

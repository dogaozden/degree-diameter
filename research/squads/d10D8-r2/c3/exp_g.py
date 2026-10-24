"""Exp G: position rule nu(p -> l) = s * k mod c (k = position of p on line l in the hexgen2 point list), explicit
matchings (identity, shift N//3), constant matching voltages (1, b). q = 4. For each (c, b) scan s and stop at the
first DIAMETER_OK. Also records the first passing s for product rule at c = 14 (s scan)."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexpos(s, c):
    return [(s * (k % Q1)) % c for l in range(N) for k in range(Q1)]
def hexprod(s, c):
    return [(s * pl[l * Q1 + k] * l) % c for l in range(N) for k in range(Q1)]
t0 = time.time()
plan = [("position", 14, [(1, 5), (1, 3)]), ("position", 15, [(1, 4), (1, 5)]), ("position", 16, [(1, 5)]),
        ("product", 14, [(1, 5)])]
for rule, c, mus in plan:
    for (a, b) in mus:
        found = None; trace = []
        for s in range(1, c):
            hv = hexpos(s, c) if rule == "position" else hexprod(s, c)
            path = "%s/G_q%d_%s_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, rule, c, a, b, s)
            mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
            F = mk.evaluate(q, path, "cyc %d" % c); trace.append((s, F))
            if F == 0: found = s; break
        print("%s c=%d mu=(%d,%d): first DIAMETER_OK s=%s | trace %s" % (rule, c, a, b, found, trace), flush=True)
print("time %.1fs" % (time.time() - t0))

"""Exp I: last scan for c = 16 at q = 4 (position rule s*k and product rule s*p*l, matchings identity / shift N//3,
constant (1, b)), early stop; then q = 2 and q = 3 checks of the best explicit candidates (c = 15, 14)."""
import time, mk
q = 4
N, Q1, pl, co = mk.load_hex(q)
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
def hexpos(s, c): return [(s * (k % Q1)) % c for l in range(N) for k in range(Q1)]
def hexprod(s, c): return [(s * pl[l * Q1 + k] * l) % c for l in range(N) for k in range(Q1)]
t0 = time.time()
for rule, c, a, b in [("position", 16, 1, 4), ("product", 16, 1, 3), ("product", 16, 1, 6)]:
    found = None; trace = []
    for s in range(1, c):
        hv = hexpos(s, c) if rule == "position" else hexprod(s, c)
        path = "%s/I_q%d_%s_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, q, rule, c, a, b, s)
        mk.write_sol(path, q, 2, c, "cyc %d" % c, [sig1, sig2], [[a] * N, [b] * N], hv)
        F = mk.evaluate(q, path, "cyc %d" % c); trace.append((s, F))
        if F == 0: found = s; break
    print("%s c=%d mu=(%d,%d): first DIAMETER_OK s=%s, min misses %s" % (rule, c, a, b, found,
          min((x for x in trace if x[1] is not None), key=lambda x: x[1])), flush=True)
# q = 2 and q = 3 checks of the explicit candidates (same rule definitions, other q)
for qq in (2, 3):
    N2, Q12, pl2, co2 = mk.load_hex(qq)
    sg1 = list(range(N2)); sg2 = [(p + N2 // 3) % N2 for p in range(N2)]
    for rule, c, a, b, s in [("position", 15, 1, 3, 7), ("position", 14, 1, 5, 2), ("product", 14, 1, 5, 2),
                             ("position", 13, 1, 5, 2)]:
        if rule == "position": hv = [(s * (k % Q12)) % c for l in range(N2) for k in range(Q12)]
        else: hv = [(s * pl2[l * Q12 + k] * l) % c for l in range(N2) for k in range(Q12)]
        path = "%s/J_q%d_%s_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, qq, rule, c, a, b, s)
        mk.write_sol(path, qq, 2, c, "cyc %d" % c, [sg1, sg2], [[a] * N2, [b] * N2], hv)
        print("q=%d %s c=%d mu=(%d,%d) s=%d: fullcost=%s" % (qq, rule, c, a, b, s, mk.evaluate(qq, path, "cyc %d" % c)), flush=True)
print("time %.1fs" % (time.time() - t0))

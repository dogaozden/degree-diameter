"""Exp J: the c = 16 product candidate (s = 6, mu = (1, 6)) at q = 2 and q = 3 (same formulas, other hexgen2 data)."""
import mk
for qq in (2, 3):
    N2, Q12, pl2, co2 = mk.load_hex(qq)
    sg1 = list(range(N2)); sg2 = [(p + N2 // 3) % N2 for p in range(N2)]
    c, a, b, s = 16, 1, 6, 6
    hv = [(s * pl2[l * Q12 + k] * l) % c for l in range(N2) for k in range(Q12)]
    path = "%s/J_q%d_product_c%d_%d_%d_s%d.sol" % (mk.OUTDIR, qq, c, a, b, s)
    mk.write_sol(path, qq, 2, c, "cyc %d" % c, [sg1, sg2], [[a] * N2, [b] * N2], hv)
    print("q=%d product c=%d mu=(%d,%d) s=%d: fullcost=%s" % (qq, c, a, b, s, mk.evaluate(qq, path, "cyc %d" % c)), flush=True)

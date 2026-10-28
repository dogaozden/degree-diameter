"""Order of level graphs over W(q): L levels, degree Delta = q+1+e, order L*2(q+1)(q^2+1); ratio to lab record at D=5."""
REC = {5: 354, 6: 684, 7: 1152, 8: 2048, 9: 2662, 10: 4800, 11: 7020, 12: 9840, 13: 11486, 14: 17568, 15: 20736, 16: 33792}
def pp(q): return all(q % p for p in range(2, q)) or any(q == p**k for p in (2,3,5,7,11,13) for k in range(2,5))
qs = [q for q in range(2, 20) if pp(q)]
for D in range(5, 17):
    best = None
    for q in qs:
        e = D - q - 1
        if e < 1: continue
        for L in (2*e+1,):
            n = L*2*(q+1)*(q*q+1)
            if best is None or n > best[0]: best = (n, q, e, L)
    n, q, e, L = best
    print('Delta=%2d  best q=%2d e=%d L=%d n=%6d  record=%6d  ratio=%.4f' % (D, q, e, L, n, REC[D], n/REC[D]))

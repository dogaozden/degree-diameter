"""Ceilings of the level-graph construction of D5_QUADRANGLE.md per cell (Delta, 5) (job d5-relax; section 14).

Order = (2r+1) * 2N(q) + K_A + K_B with Delta = q+1+r.  Bounds used, each one a statement of the note:
  * every freed set on a friendly arc has at most B(q) = floor(2(q+1)(q^2+1)/(2q+1)) elements (counting bound; it holds
    for partial ovoids, partial spreads and relaxed sets of points or of lines), and an H->D freed set with M = id is a
    partial ovoid of Q(4,q), at most q^2+1 points (Theorem B; used in the 'a = q^2+1' column);
  * at most c elements per non-friendly arc (c = 2 for local dualities, Corollary 6.2);
  * K_B <= min_j alpha_j, K_A <= min_j beta_j, and sum_j alpha_j = sum_j beta_j = sum_t |R_t| (each arc counted
    once), so K_A + K_B <= 2 * sum_t |R_t| / (2r+1) <= 2r * max_t |R_t|  (any layout);
  * for q odd and 5, 7, 9 levels the best typed layouts of section 8 (computer-checked optimal over all regular
    tournaments and typings): 2b+2c, min(a+b+4c, 3b+3c), 4b+4c.
usage: python3 ceilings.py [c]"""
import sys

def N(q): return (q + 1) * (q * q + 1)
def B(q): return 2 * (q + 1) * (q * q + 1) // (2 * q + 1)
PP = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19]
c = int(sys.argv[1]) if len(sys.argv) > 1 else 2
lab = {10: 4800, 11: 7020, 12: 9840, 13: 11700, 14: 17568, 15: 20736, 16: 33792}
print('c = %d freed elements per non-friendly arc' % c)
print('Delta  lab     best ceiling (q, r, levels)            ceiling with a = q^2+1 (same (q,r))')
for D in range(10, 18):
    rows = []
    for q in PP:
        r = D - q - 1
        if r < 1 or r > q - 1: continue                     # hubs need q - r >= 1
        base = (2 * r + 1) * 2 * N(q)
        b = B(q); a = b
        if q % 2 == 1 and r in (2, 3, 4):
            K = {2: 2 * b + 2 * c, 3: min(a + b + 4 * c, 3 * b + 3 * c), 4: 4 * b + 4 * c}[r]
            K0 = {2: 2 * b + 2 * c, 3: min(q * q + 1 + b + 4 * c, 3 * b + 3 * c), 4: 4 * b + 4 * c}[r]
        else:
            K = K0 = 2 * r * max(b, c)
        rows.append((base + K, base + K0, q, r))
    best = max(rows)
    print('%3d  %7s   %7d (q=%d, r=%d, %d levels)        %7d' % (D, '{:,}'.format(lab[D]) if D in lab else '-', best[0],
                                                             best[2], best[3], 2 * best[3] + 1, best[1]))

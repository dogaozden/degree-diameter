"""Check m = (2j+1)(floor((q-1)/2) + 3(j-1)) against the six green D = 8 table values m*|GH(q)| (Δ = q+1+j)."""
def gh(q): return 2 * (q + 1) * (q ** 4 + q * q + 1)
cells = {(10, 8): 1176480, (11, 8): 2246940, (12, 8): 4650100, (13, 8): 5314680, (14, 8): 14172480, (16, 8): 36201060}
fits = {(10, 8): (7, 2), (11, 8): (8, 2), (12, 8): (9, 2), (13, 8): (11, 1), (14, 8): (11, 2), (16, 8): (13, 2)}
out = []
for c, (q, j) in fits.items():
    m = (2 * j + 1) * ((q - 1) // 2 + 3 * (j - 1))
    out.append(f"{c}: q={q} j={j} Δ={q+1+j} m={m} m*|GH(q)|={m*gh(q)} table={cells[c]} {'OK' if m*gh(q)==cells[c] else 'NO'}")
open('d8_formula_out.txt', 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))

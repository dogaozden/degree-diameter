"""Numerology of the green (Delorme-Gomez-Quisquater) D = 8 cells against |GH(q)| and table constraints.

Prints: (1) the six cells as M * |GH(q)| with Delta = q + 1 + j; (2) closed forms; (3) for every (q, j) with
q+1+j <= 16 the largest multiplier M that the table value allows (M_max = floor(table(Delta,8) / |GH(q)|)) -- since
DGQ entered the best value they had in each cell, their construction gives at most M_max at (q, j)."""
import math

TABLE8 = {3: 256, 4: 2184, 5: 9234, 6: 29790, 7: 80940, 8: 201480, 9: 449480, 10: 1176480, 11: 2246940,
          12: 4650100, 13: 5314680, 14: 14172480, 15: 14172480, 16: 36201060}
GREEN = {3, 10, 11, 12, 13, 14, 15, 16}   # wiki colour key (research/lifts LITERATURE.md, branch voltage-lifts-search)
PP = [2, 3, 4, 5, 7, 8, 9, 11, 13]


def gh(q):
    return 2 * (q ** 6 - 1) // (q - 1)


print('(1) green D=8 cells as multiples of |GH(q)|')
for D_, val in sorted(TABLE8.items()):
    hits = [(q, D_ - q - 1, val // gh(q)) for q in PP if val % gh(q) == 0 and D_ - q - 1 >= 0]
    if hits:
        print(f'  ({D_},8) = {val:>10,} = ' + ', '.join(f'{m}*|GH({q})| (j={j})' for q, j, m in hits))
print()
print('(2) closed forms for the five j=2 cells: M = 5*floor((q+5)/2) = 5*(floor((q+1)/2) + 2)')
for q in [7, 8, 9, 11, 13]:
    M = 5 * ((q + 5) // 2)
    flags = (q + 1) * (q ** 6 - 1) // (q - 1)
    P = (q ** 6 - 1) // (q - 1)
    print(f'  q={q:2d} Delta={q+3:2d}: M={M} table/|GH|={TABLE8[q+3]/gh(q):.4f}; '
          f'10|GH|+5*flags={10*gh(q)+5*flags:,} (odd q), 10|GH|+5*(flags-P)={10*gh(q)+5*(flags-P):,} (even q); '
          f'table {TABLE8[q+3]:,}')
print()
print('(3) M_max(q, j) = floor(table(q+1+j, 8) / |GH(q)|): DGQ construction gives <= this at (q, j)')
print('   q \\ j ' + ''.join(f'{j:>8d}' for j in range(0, 6)))
for q in PP:
    row = []
    for j in range(0, 6):
        D_ = q + 1 + j
        row.append(f'{TABLE8[D_] // gh(q):>8d}' if D_ in TABLE8 else '       -')
    print(f'  {q:5d}  ' + ''.join(row))

"""The j = 2 counting bound (D8_NUMEROLOGY.md §1.2) against DGQ's formula.

For two matchings, a regular zero-holonomy labelling covered by the guaranteed walks alone has
M <= 1 + 2(q+1)(q+4)/(q-3) (q > 3).  DGQ's multiplier is 5*floor((q+5)/2).  Prints both."""
from fractions import Fraction


def bound(q):
    return 1 + Fraction(2 * (q + 1) * (q + 4), q - 3)


def dgq(q):
    return 5 * ((q + 5) // 2)


print('q  bound(floor)  exact            DGQ  DGQ>bound')
for q in [4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]:
    b = bound(q)
    print(f'{q:<3} {int(b):<12} {str(b):<16} {dgq(q):<4} {dgq(q) > b}')

"""Tight one-matching guaranteed-walk designs (M = q + 4): the inequality of D8_NUMEROLOGY.md §1.5.
For a regular one-miss design, some label d has s = a_{-d} + n_{-d} >= 2P/(q+3), and
  s(P - s)/P  <=  q/(q-1)^2 * ( sqrt(P/(q+1)) + sqrt(P/4) )^2 .
With s <= 2P/(q+1) <= P/2 the left side is at least 2P(q+1)/(q+3)^2.  Prints both sides divided by P."""
from math import sqrt
print(' q   LHS/P (lower)   RHS/P (upper)   contradiction')
for q in [3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31]:
    lhs = 2 * (q + 1) / (q + 3) ** 2
    rhs = q / (q - 1) ** 2 * (1 / sqrt(q + 1) + 0.5) ** 2
    print(f'{q:2d}   {lhs:.4f}          {rhs:.4f}          {lhs > rhs}')

"""thm2_bound.py (referee omega-dq): the counting bound of Theorem 2 in research/squads/cells/d12D8_table.md, recomputed
two ways: from the closed forms A, B given there, and by summing sphere sizes s_0 = 1, s_i = (q+1) q^(i-1) of the
incidence graph of H(q) over the walk shapes of the proof:
  start at t, 1 switch:          sum of s_e1 s_e2 over e1 + e2 in {0, 2, 4}                  (A)
  start at sigma(t), 2 switches: sum of s_e1 s_e2 s_e3 over e1 + e2 + e3 <= 2                 (B)
  start at t, 3 switches:        1 vertex (sigma(t) itself)
  start at sigma(t), 0 switches: within distance 4, never opposite.
The theorem needs A + B + 1 < q^5 (the number of vertices opposite a given vertex)."""
from itertools import product
def s(i, q): return 1 if i == 0 else (q + 1) * q ** (i - 1)
print(f"{'q':>3} {'A':>8} {'B':>6} {'A+B+1':>8} {'q^5':>8} {'q^5-(A+B+1)':>12}  closed forms agree  bound holds")
for q in range(2, 17):
    A = sum(s(a, q) * s(b, q) for a, b in product(range(5), repeat=2) if a + b in (0, 2, 4))
    B = sum(s(a, q) * s(b, q) * s(c, q) for a, b, c in product(range(3), repeat=3) if a + b + c <= 2)
    Ac = 1 + 2*q*(q+1) + (q+1)**2 + 2*q**3*(q+1) + 3*q**2*(q+1)**2
    Bc = 1 + 3*(q+1) + 3*q*(q+1) + 3*(q+1)**2
    T = A + B + 1
    print(f"{q:>3} {A:>8} {B:>6} {T:>8} {q**5:>8} {q**5 - T:>12}  {str(A == Ac and B == Bc):>18}  {str(T < q**5):>11}")

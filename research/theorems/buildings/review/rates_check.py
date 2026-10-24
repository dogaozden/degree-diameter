from fractions import Fraction
import sys
sys.path.insert(0, '/tmp/claude-0/-home-user-degree-diameter/bca0bf0f-5904-53d7-a35c-bf89127b664f/scratchpad/review')
from thick_check import predict
def qint(d, q): return (q**d - 1) // (q - 1)
def Mb(D, Dl): return 2 * sum((D - 1)**i for i in range(Dl))
def Mg(D, Dl): return 1 + D * sum((D - 1)**i for i in range(Dl))
def is_pp(n):
    if n < 2: return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1
        p += 1
    return True
routes = {  # D: (degrees, rank, t or None for Delorme)
  5: ([2,3,4,5], 4, 2), 7: ([2,3,4,5,6,7], 6, 3), 8: ([2,4,6,8], 4, 2), 9: (list(range(2,10)), 8, 4),
  10: ([2,4,6,8,10], 5, None), 12: ([2,6,8,12], 4, 2), 16: ([2,4,6,8,10,12,14,16], 8, 4),
  18: ([2,6,8,10,12,14,18], 7, None), 30: ([2,8,12,14,18,20,24,30], 8, 4)}
def ratio(D, q):
    degs, rk, t = routes[D]
    E = 1
    for d in degs: E *= qint(d, q)
    if t is None: n = 2 * E * E // (q + 1)**rk; Delta = (q + 1)**rk
    else: n = 2 * E // (q + 1)**t; Delta = (q + 1)**t
    return n / Mb(Delta, D), Delta, q
for D in sorted(routes):
    f50 = f90 = None; q = 2
    while f90 is None:
        if is_pp(q):
            r, Delta, _ = ratio(D, q)
            if f50 is None and r >= 0.5: f50 = (q, Delta)
            if r >= 0.9: f90 = (q, Delta)
        q += 1
    print(f"D={D}: 50% first at q={f50[0]} Delta={f50[1]:.3g}; 90% at q={f90[0]} Delta={f90[1]:.3g}")
# D=12 comparisons at q=16
q = 16
E_F4 = 1
for d in [2,6,8,12]: E_F4 *= qint(d, q)
E_E6 = 1
for d in [2,5,6,8,9,12]: E_E6 *= qint(d, q)
num = (q**2-1)*(q**5+1)*(q**6-1)*(q**8-1)*(q**9+1)*(q**12-1); den = (q-1)**2*(q**2-1)**2; E_2E6 = num // den
for name, E, Delta in [('F4', E_F4, (q+1)**2), ('E6', E_E6, (q+1)**3), ('2E6', E_2E6, (q+1)*(q**2+1))]:
    n = 2 * E // Delta
    print(f"q=16 {name}: Delta={Delta} n/Mb(Delta,12) = {n / Mb(Delta, 12):.3f}")
# B3 quotient at q=16, general Moore bound, D=5
E = qint(2,16)*qint(4,16)*qint(6,16); Delta = 17**3
print("B3(16) quotient: |Q|/Moore_general(4913,5) =", round((E*E // Delta) / Mg(Delta, 5), 3))
# PG(4,3) layers
I, P, out = predict('A', 4, [3,3,3,3])
print("PG(4,3) layers:", out[(0,0)], out[(0,1)])
I, P, out = predict('B', 4, [2,2,2,2])
print("Sp(8,2) layers same side from I1 / I2:", out[(0,0)], out[(1,1)])

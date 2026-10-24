"""Independent exact-arithmetic check of Theorem 4 (a)-(c) first-order constants, and of the 2E6 parameters."""
from fractions import Fraction
import sys
sys.path.insert(0, '/tmp/claude-0/-home-user-degree-diameter/bca0bf0f-5904-53d7-a35c-bf89127b664f/scratchpad/review')
import numpy as np
from thin_check import coxeter_matrix, group, colour

def qint(d, q): return (q**d - 1) // (q - 1)
def Mb(D, Dl): return 2 * sum((D - 1)**i for i in range(Dl))
types = {  # name: (degrees, h, |I1|, |I2|)
 'A4': ([2,3,4,5], 5, 2, 2), 'A6': ([2,3,4,5,6,7], 7, 3, 3), 'C4': ([2,4,6,8], 8, 2, 2),
 'F4': ([2,6,8,12], 12, 2, 2), 'E6': ([2,5,6,8,9,12], 12, 3, 3), 'E8': ([2,8,12,14,18,20,24,30], 30, 4, 4),
 'A3': ([2,3,4], 4, 2, 1), 'B5': ([2,4,6,8,10], 10, 3, 2), 'E7': ([2,6,8,10,12,14,18], 18, 3, 4)}
for q in (10**6 + 3, 10**7 + 19):
    for name in ('A4', 'A6', 'C4', 'F4', 'E6', 'E8'):
        degs, h, a, b = types[name]; t = a
        E = 1
        for d in degs: E *= qint(d, q)
        n = 2 * E // (q + 1)**t
        Delta = (q + 1)**t
        r = Fraction(n, Mb(Delta, h))
        print(f"q={q} {name}: q(1-n/Mb) = {float(q*(1-r)):.5f}   predicted t(h-2) = {t*(h-2)}")
    for name in ('A3', 'B5', 'E7'):
        degs, h, a, b = types[name]; rk = a + b
        E = 1
        for d in degs: E *= qint(d, q)
        n = 2 * E * E // (q + 1)**rk
        Delta = (q + 1)**rk
        r = Fraction(n, Mb(Delta, h))
        print(f"q={q} {name} Delorme: q(1-n/Mb) = {float(q*(1-r)):.5f}   predicted r(h-2) = {rk*(h-2)}")

# 2E6: weighted Poincare polynomial of W(F4), nodes {0,1} weight q, {2,3} weight q^2 (two adjacent nodes q)
M = coxeter_matrix('F', 4); S, elems, length, key = group(M)
e = np.eye(4); wt = {key(e): 0}; fr = [e]
w8 = [1, 1, 2, 2]
while fr:
    nf = []
    for A in fr:
        ka = key(A)
        for i, s in enumerate(S):
            B = s @ A; kb = key(B)
            if length[kb] == length[ka] + 1:
                if kb not in wt: wt[kb] = wt[ka] + w8[i]; nf.append(B)
                else: assert wt[kb] == wt[ka] + w8[i]
    fr = nf
from collections import Counter
poly = Counter(wt.values())
print("2E6 top exponent", max(poly), "coefficient of q^35:", poly[35], " of q^36:", poly[36])
for q in (2, 3, 4, 5, 7):
    E1 = sum(c * q**k for k, c in poly.items())
    num = (q**2-1)*(q**5+1)*(q**6-1)*(q**8-1)*(q**9+1)*(q**12-1); den = (q-1)**2*(q**2-1)**2
    assert num % den == 0
    print(f"q={q}: W(F4) weighted sum = {E1}, |2E6(q)|/|B| = {num//den}, equal: {E1 == num//den}")
I = colour(M); print("F4 colour classes", I, "-> each class has one weight-1 and one weight-2 node:",
                     all(sorted(w8[i] for i in Ik) == [1, 2] for Ik in I))
for q in (10**6 + 3,):
    E = sum(c * q**k for k, c in poly.items())
    D = (q + 1) * (q**2 + 1); n = 2 * E // D
    r = Fraction(n, Mb(D, 12)); print(f"2E6 q={q}: q(1-n/Mb) = {float(q*(1-r)):.5f}  predicted 10")

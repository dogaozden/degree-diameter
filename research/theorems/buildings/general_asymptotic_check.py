"""First-order constants for general graphs (BUILDINGS.md §1.7(f)): q (1 - |Q|/M(Delta, D)) at large primes q, with
M the general Moore bound.  Predicted: D(D-1) for Delorme's quotient of the A_D flag graph (Delta = (q+1)^D);
r(D-1), r = (D+1)/2, for the quotient of the B_r flag graph (D odd, Delta = (q+1)^r); for comparison CvB-K's H_{D,q}
with their degree bound K_q = (q+1)^D ((q+1)^D - 1), predicted D(2D-1) (their Remark 3.2)."""
import sys
from fractions import Fraction
sys.path.insert(0, '.')
from rates import E, DEG
def M(d, D): return 1 + d * sum((d - 1) ** i for i in range(D))
for D in (3, 4, 5):
    for q in (1009, 10007, 100003):
        A = E(DEG['A'](D), q) ** 2 // (q + 1) ** D; dA = (q + 1) ** D
        line = f"D={D} q={q}: A{D} quotient q(1-|Q|/M)={float(q * (1 - Fraction(A, M(dA, D)))):.4f} (pred {D*(D-1)})"
        if D % 2:
            r = (D + 1) // 2
            Bq = E(DEG['B'](r), q) ** 2 // (q + 1) ** r; dB = (q + 1) ** r
            line += f";  B{r} quotient {float(q * (1 - Fraction(Bq, M(dB, D)))):.4f} (pred {r*(D-1)})"
        N = E(DEG['A'](2 * D), q) // (q + 1) ** D; K = (q + 1) ** D * ((q + 1) ** D - 1)
        line += f";  H_(D,q) with degree bound {float(q * (1 - Fraction(N, M(K, D)))):.4f} (pred {D*(2*D-1)})"
        print(line)

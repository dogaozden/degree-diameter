"""Item 5: regularities in the table values (DS14v2 Table 4 = research/frontier/TABLE.md).
For every cell (Δ, D) with D = 5..10, test whether the table value is m * |polygon incidence graph of order q| for
a generalized n-gon (n = 3, 4, 6: plane, GQ W(q), hexagon H(q)) with q a prime power, and print the factorisation."""
import sys
sys.path.insert(0, '../frontier')
from heuristic import TABLE, moore
from sympy import factorint

def pp(q):
    f = factorint(q); return len(f) == 1
PQ = [q for q in range(2, 40) if pp(q)]
POLY = {3: lambda q: 2*(q*q+q+1), 4: lambda q: 2*(q+1)*(q*q+1), 6: lambda q: 2*(q+1)*(q**4+q*q+1)}
def fmt(n): return '·'.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(factorint(n).items()))
print("cell  table  factorisation  | fits m*|Γ_n(q)| with Δ = q+1+j (j = Δ-q-1 >= 0), m small")
for D in range(5, 11):
    for d in range(3, 17):
        t = TABLE[d][D-3]
        if t is None: continue
        fits = []
        for n, f in POLY.items():
            for q in PQ:
                j = d - q - 1
                if j < 0: continue
                g = f(q)
                if t % g == 0 and t // g <= 200:
                    fits.append(f"m={t//g}·Γ{n}(q={q}),j={j}")
        print(f"({d},{D}) {t} = {fmt(t)}  ratio/Moore={t/moore(d,D):.4f}  " + ('; '.join(fits) if fits else '-'))
    print()

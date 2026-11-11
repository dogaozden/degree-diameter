# Integrality check from Feria-Puron & Pineda-Villavicencio (arXiv 1010.5651), Prop. 5.1 (PDF p.15-16):
# a bipartite (d,D,-4)-graph has N = (2S-4)/(D-1) short cycles, S = sum_{i=0}^{D-1} (d-1)^i (order = 2S-4).
# S mod (D-1) depends only on (d-1) mod (D-1), so one period of length (D-1) decides all d.
import sys
D = int(sys.argv[1]) if len(sys.argv) > 1 else 12
m = D - 1
ok = []
for x in range(0, m):  # x = d-1 mod m
    S = sum(pow(x, i, m) for i in range(D)) % m
    if (2 * S - 4) % m == 0:
        ok.append(x)
print(f"D={D}: residues x=d-1 mod {m} with (D-1) | (2S-4): {ok if ok else 'none'}")

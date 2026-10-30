# make_direct3.py R.bh OUT.bh : table of G = R x C3 (element (r,c) has index 3r+c, identity 0), with one
# "H 1 n" line (H = 1 x C3, central).  Used to calibrate bic3: the bi-coset graph with H = C3 and D = S x C3 is the
# Haar graph H(R,S).  usage: python3 make_direct3.py R.bh OUT.bh   (run with -I)
import sys
src, out = sys.argv[1], sys.argv[2]
with open(src) as f:
    toks = f.read().split()
n = int(toks[0]); pos = 2
R = [[int(toks[pos + i * n + j]) for j in range(n)] for i in range(n)]; pos += n * n
invR = [int(x) for x in toks[pos:pos + n]]
m = 3 * n
with open(out, "w") as f:
    f.write(f"{m} 0\n")
    for a in range(n):
        for c1 in range(3):
            row = []
            for b in range(n):
                for c2 in range(3):
                    row.append(3 * R[a][b] + (c1 + c2) % 3)
            f.write(" ".join(map(str, row)) + "\n")
    row = []
    for r in range(n):
        for c in range(3):
            row.append(3 * invR[r] + (3 - c) % 3)
    f.write(" ".join(map(str, row)) + "\n")
    f.write(f"H 1 {m}\n")
print("wrote", out, "n =", m)

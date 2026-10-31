# usage: python3 -I grp_tab.py KIND M OUT : KIND = cyc (Z_M) or z7z7 (Z_7 x Z_7 for M=49, element a*7+b)
import sys
kind, M, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
if kind == 'cyc':
    tab = [[(a + b) % M for b in range(M)] for a in range(M)]
elif kind == 'z7z7':
    tab = [[((a // 7 + b // 7) % 7) * 7 + ((a % 7 + b % 7) % 7) for b in range(M)] for a in range(M)]
with open(out, 'w') as f:
    f.write(f"{M}\n")
    for row in tab:
        f.write(" ".join(map(str, row)) + "\n")
print("wrote", out)

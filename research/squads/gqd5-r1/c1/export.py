import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W
G = W(9)
n = G.np
with open('graph_W9.txt', 'w') as f:
    f.write(f"{n}\n")
    for i in range(n):
        nb = [j for j in range(n) if j != i and G.col[i, j]]
        f.write(str(len(nb)) + " " + " ".join(map(str, nb)) + "\n")
print("ok", n)

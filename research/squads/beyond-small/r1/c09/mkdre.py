import sys
sys.argv = ['x']
from gq import build
G = build(8)
N = G['N']; V = 2 * N
out = [f"n={V} g"]
for v in range(V):
    nb = [u for u in range(V) if G['nbr'][v] >> u & 1]
    out.append(f"{v} : " + " ".join(map(str, nb)) + ";")
out.append(".")
out.append("a")
out.append("x")
out.append("q")
open('/home/user/degree-diameter/research/squads/beyond-small/r1/c09/w8.dre', 'w').write("\n".join(out) + "\n")

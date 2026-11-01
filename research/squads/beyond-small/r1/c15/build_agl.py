# Rebuild the bipartite Haar graph H(AGL(1,p), S) with |S| = 17.
# usage: python3 build_agl.py P S1 ... S17 OUT.edges
# Element index x = (a-1)*P + b  encodes the affine map t -> a*t + b (a in 1..P-1, b in 0..P-1).
# Vertices: A_g = g, B_h = M + h, edges A_g -- B_{s*g} for s in S.
import sys
P = int(sys.argv[1]); S = [int(v) for v in sys.argv[2:-1]]; OUT = sys.argv[-1]
M = P * (P - 1)
def dec(x): return x // P + 1, x % P
def mul(x, y):
    a, b = dec(x); c, d = dec(y)
    return (((a * c) % P) - 1) * P + (a * d + b) % P
assert len(S) == 17 and len(set(S)) == 17
with open(OUT, "w") as f:
    f.write(f"{2*M}\n")
    for s in S:
        for g in range(M):
            f.write(f"{g} {M + mul(s, g)}\n")
print("wrote", OUT, "n =", 2 * M)

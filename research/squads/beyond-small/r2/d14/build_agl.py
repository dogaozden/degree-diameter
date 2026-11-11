# build bi-Cayley graph over AGL(1,p): (g,0)=g, (g,1)=N+g ; edges g -- N + s*g for s in S
# usage: build_agl.py P statefile out.edges
import sys
P = int(sys.argv[1]); N = P * (P - 1)
S = [int(x) for x in open(sys.argv[2]).read().split()]
assert len(S) == 17 and len(set(S)) == 17
def dec(g): return g // P + 1, g % P
def enc(a, b): return (a - 1) * P + b
def mul(x, y):
    a1, b1 = dec(x); a2, b2 = dec(y)
    return enc((a1 * a2) % P, (a1 * b2 + b1) % P)
with open(sys.argv[3], "w") as f:
    f.write(f"{2 * N}\n")
    for s in S:
        for g in range(N):
            f.write(f"{g} {N + mul(s, g)}\n")
print("wrote", 2 * N, "vertices", 17 * N, "edges")

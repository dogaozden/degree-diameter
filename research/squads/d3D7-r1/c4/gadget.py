"""c4: insert one vertex pair (X white, Y black) into the H-quotient base by the gadget
   delete (A1,B1,a1),(A2,B2,a2); add X-Y(0), X-B1(a1), X-B2(a2), Y-A1(0), Y-A2(0).
Usage: gadget.py BASE.sol SEED OUT.sol   (base file: "N id p" then "u v a" lines, white u < p, black v >= p)"""
import sys, random
src, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
L = open(src).read().split()
N, gid, p = int(L[0]), int(L[1]), int(L[2])
E = [(int(L[3+3*i]), int(L[4+3*i]), int(L[5+3*i])) for i in range((len(L)-3)//3)]
rnd = random.Random(seed)
while True:
    i, j = rnd.sample(range(len(E)), 2)
    (A1, B1, a1), (A2, B2, a2) = E[i], E[j]
    if A1 != A2 and B1 != B2: break
rest = [e for k_, e in enumerate(E) if k_ not in (i, j)]
X = p; Y = 2*p + 1; P = p + 1
def shift(v): return v if v < p else v + 1   # old black v -> v+1
new = [(shift(u), shift(v), a) for (u, v, a) in rest]
new += [(X, Y, 0), (X, shift(B1), a1), (X, shift(B2), a2), (A1, Y, 0), (A2, Y, 0)]
# shifted whites are unchanged (u < p < X), blacks shifted by one; Y = 2p+1 is last
with open(out, "w") as f:
    f.write(f"{N} {gid} {P}\n")
    for (u, v, a) in new: f.write(f"{u} {v} {a}\n")
print(f"gadget seed={seed} A1={A1} B1={B1} a1={a1} A2={A2} B2={B2} a2={a2} -> p={P} edges={len(new)}", file=sys.stderr)

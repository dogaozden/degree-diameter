import sys
m, k, r = 677, 13, 362
S = [0, 153*k + 9, 562*k + 10]
N = m * k
def mul(x, y):
    a, j = divmod(x, k); b, l = divmod(y, k)
    return ((a + pow(r, j, m) * b) % m) * k + (j + l) % k
out = [f"{2*N}"]
for g in range(N):
    for s in S:
        out.append(f"{g} {N + mul(s, g)}")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
print(len(out) - 1, "edges")

"""inner_phi.py GROUPS id out: phi = conjugation by an element t of order 3 (N ints), checked as an automorphism."""
import sys
tok = open(sys.argv[1]).read().split()
want = int(sys.argv[2]); i = 0
while True:
    N, g = int(tok[i+1]), int(tok[i+2]); i += 4
    if g == want: mul = [[int(tok[i+r*N+c]) for c in range(N)] for r in range(N)]; break
    i += N*N
e = 0
inv = [next(b for b in range(N) if mul[a][b] == e) for a in range(N)]
def order(x):
    k, y = 1, x
    while y != e: y = mul[y][x]; k += 1
    return k
t = next(x for x in range(N) if order(x) == 3)
phi = [mul[mul[t][g]][inv[t]] for g in range(N)]
for a in range(N):
    for b in range(N):
        assert mul[phi[a]][phi[b]] == phi[mul[a][b]]
assert all(phi[phi[phi[a]]] == a for a in range(N))
open(sys.argv[3], "w").write("\n".join(map(str, phi)) + "\n")
print("N", N, "t", t, "phi", phi, "fixed", sum(phi[a]==a for a in range(N)))

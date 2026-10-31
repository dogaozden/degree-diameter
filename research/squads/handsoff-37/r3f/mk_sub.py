# mk_sub.py GROUPFILE STATE OUTSTATE SUBORDER: derive a lift over a free cyclic subgroup H = <x> (order SUBORDER)
# of the group (abelian) from a lift state. Base vertex (u,c) for coset c of H; state "k' ' lines "u v a" with
# voltage = H-exponent. Output state for groups/C<SUBORDER>.txt (cyclic table, identity 0).
import sys
gf, sf, outp, so = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
L = open(gf).read().split(); N = int(L[0]); T = [[int(L[1 + a * N + b]) for b in range(N)] for a in range(N)]
S = open(sf).read().split('\n'); NN, k = map(int, S[0].split())
E = [tuple(map(int, l.split())) for l in S[1:] if l.strip()]
assert NN == N
def power(x, e):
    r = 0
    for _ in range(e): r = T[r][x]
    return r
def order(x):
    o, y = 1, x
    while y != 0: y = T[y][x]; o += 1
    return o
x = next(g for g in range(N) if order(g) == so)
H = [power(x, i) for i in range(so)]
assert len(set(H)) == so
# coset reps
reps = [0]; cos = {}
for i in range(so): cos[H[i]] = (0, i)
for g in range(N):
    if g in cos: continue
    t = g; reps.append(t)
    for i in range(so): cos[T[t][H[i]]] = (len(reps) - 1, i)
C = len(reps); assert C * so == N
newk = C * k
out = [f"{so} {newk}"]
for (u, v, a) in E:
    for c in range(C):
        w = T[reps[c]][a]
        d, j = cos[w]
        out.append(f"{u * C + c} {v * C + d} {j}")
open(outp, 'w').write('\n'.join(out) + '\n')
print("subgroup order", so, "cosets", C, "new k", newk, "base edges", len(out) - 1)

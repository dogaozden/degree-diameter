# usage: gen_meta.py m r k OUT   -> group Z_m x|_r Z_k, element (i,j) index i*k+j, identity index 0
import sys
m, r, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
assert pow(r, k, m) == 1 % m, "r^k != 1"
h = m * k
def idx(i, j): return i * k + j
rows = []
for i1 in range(m):
    for j1 in range(k):
        for i2 in range(m):
            for j2 in range(k):
                pass
M = [[0]*h for _ in range(h)]
for i1 in range(m):
    for j1 in range(k):
        for i2 in range(m):
            for j2 in range(k):
                M[idx(i1,j1)][idx(i2,j2)] = idx((i1 + pow(r, j1, m) * i2) % m, (j1 + j2) % k)
with open(sys.argv[4], "w") as f:
    f.write(f"{h}\n")
    for row in M:
        f.write(" ".join(map(str, row)) + "\n")
# sanity: identity at 0, associativity sample
import random
for _ in range(2000):
    a,b,c = [random.randrange(h) for _ in range(3)]
    assert M[M[a][b]][c] == M[a][M[b][c]]
assert all(M[0][x] == x and M[x][0] == x for x in range(h))
print("ok h =", h)

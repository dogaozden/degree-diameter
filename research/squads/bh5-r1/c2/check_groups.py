import sys, random
for fn in sys.argv[1:]:
    L = open(fn).read().split()
    m = int(L[0]); T = [[int(L[1 + i*m + j]) for j in range(m)] for i in range(m)]
    ok = all(T[0][j] == j for j in range(m)) and all(T[i][0] == i for i in range(m))
    rng = random.Random(1)
    for _ in range(3000):
        a, b, c = rng.randrange(m), rng.randrange(m), rng.randrange(m)
        if T[T[a][b]][c] != T[a][T[b][c]]: ok = False; break
    if len(set(T[0])) != m: ok = False
    if not ok: print("BAD", fn)
print("checked", len(sys.argv) - 1)

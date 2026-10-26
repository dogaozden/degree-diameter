import sys
rows = [l.split() for l in open('classes.txt')]
res = []
for m, k, r, d, N, g in rows:
    m, k, r, d, N, g = map(int, (m, k, r, d, N, g))
    inv = 0
    for j in range(k):
        rj = pow(r, j, m)
        for a in range(m):
            if j == 0 and a == 0:
                continue
            if (2 * j) % k == 0 and (a * (1 + rj)) % m == 0:
                inv += 1
    res.append((inv, m, k, r, d, N, g))
res.sort()
with open('classes_inv.txt', 'w') as f:
    for t in res:
        f.write("%d %d %d %d %d %d %d\n" % t)
for t in res[:40]:
    print(*t)

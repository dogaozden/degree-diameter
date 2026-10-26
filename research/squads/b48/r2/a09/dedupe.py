import math
rows = [tuple(map(int, l.split())) for l in open('meta.txt')]
keep = []
for N, m, k, r, o in rows:
    # orbit of r under powers coprime to o (same cyclic normal action up to generator change of Z_k)
    orb = set()
    for j in range(1, o + 1):
        if math.gcd(j, o) == 1:
            orb.add(pow(r, j, m))
    if r == min(orb):
        keep.append((N, m, k, r, o))
for x in keep:
    print(*x)

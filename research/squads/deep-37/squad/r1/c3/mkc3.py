"""Write a C3 (or trivial) group file and a degree file for c3sa on n=169 (A = 0..84, B = 85..168).
usage: mkc3.py OUTDIR FB_FIXED ORDER   (ORDER 3 or 1; FB_FIXED = number of fixed B-vertices, A has 1 fixed vertex (84)
 when ORDER=3, A's degree-2 vertices 0,1,2 form one orbit; when ORDER=1 the same degree file is used without symmetry)"""
import sys, os
out, fb, order = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
n, NA = 169, 85
A = list(range(NA)); B = list(range(NA, n))
def cyc_perm(orbits_A, fixA, orbits_B, fixB):
    p = list(range(n))
    for c in orbits_A:
        for i, x in enumerate(c): p[x] = c[(i + 1) % len(c)]
    for c in orbits_B:
        for i, x in enumerate(c): p[x] = c[(i + 1) % len(c)]
    return p
if order == 3:
    assert (NA - 1) % 3 == 0
    cA = [[3 * i, 3 * i + 1, 3 * i + 2] for i in range((NA - 1) // 3)]
    nb = B[fb:] if fb else B
    assert len(nb) % 3 == 0
    cB = [nb[3 * i: 3 * i + 3] for i in range(len(nb) // 3)]
    s = cyc_perm(cA, [84], cB, None)
    s2 = [s[s[v]] for v in range(n)]
    perms = [list(range(n)), s, s2]
else:
    perms = [list(range(n))]
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, 'group.txt'), 'w') as f:
    f.write(f"{n} {len(perms)}\n")
    for p in perms: f.write(" ".join(map(str, p)) + "\n")
    f.write(" ".join("0" if v < NA else "1" for v in range(n)) + "\n")
deg = [2 if v in (0, 1, 2) else 3 for v in range(NA)] + [3] * (n - NA)
with open(os.path.join(out, 'deg.txt'), 'w') as f:
    f.write(f"{n} {NA}\n" + " ".join(map(str, deg)) + "\n")
print("ok", out, len(perms))

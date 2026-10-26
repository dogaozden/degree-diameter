"""aut_gen.py: inner automorphisms of order 3 (conjugation by an element g with g^3 = 1) of a group table.

usage: python3 -I aut_gen.py GROUPFILE OUTPREFIX
Writes OUTPREFIX_<idx>.txt (n integers: x -> g x g^-1) for one order-3 element per conjugacy class, and prints,
per class, its index, the size of its fixed set (= centraliser of g) and the 3-orbit count (n - |Fix|)/3.
"""
import sys


def load(p):
    with open(p) as f:
        m = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(m)]
    return m, T


def main(gp, prefix):
    n, T = load(gp)
    inv = [next(y for y in range(n) if T[x][y] == 0) for x in range(n)]
    order3 = [g for g in range(n) if g != 0 and T[g][T[g][g]] == 0]
    seen = set()
    classes = []
    for g in order3:
        if g in seen:
            continue
        cls = {T[T[x][g]][inv[x]] for x in range(n)}   # conjugacy class of g
        seen |= cls
        classes.append(g)
    out = []
    for idx, g in enumerate(classes):
        perm = [T[T[g][x]][inv[g]] for x in range(n)]
        fix = sum(1 for x in range(n) if perm[x] == x)
        orbits3 = (n - fix) // 3
        path = f"{prefix}_{idx}.txt"
        with open(path, "w") as f:
            f.write(" ".join(map(str, perm)) + "\n")
        out.append((idx, g, fix, orbits3, path))
        print(f"class {idx}: g={g} |Fix|={fix} 3-orbits={orbits3} -> {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))

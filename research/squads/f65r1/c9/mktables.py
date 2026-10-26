# Build multiplication tables: groups (mode 'grp') and Chein loops M(G,2) (mode 'chein').
import sys, itertools, os
OUT = "/home/user/degree-diameter/research/squads/f65r1/c9/tables"

def closure(gens, mul, ident):
    elems = [ident]; idx = {ident: 0}; frontier = [ident]
    while frontier:
        nf = []
        for a in frontier:
            for g in gens:
                b = mul(a, g)
                if b not in idx:
                    idx[b] = len(elems); elems.append(b); nf.append(b)
        frontier = nf
    return elems, idx

def group_table(elems, idx, mul):
    n = len(elems)
    return [[idx[mul(elems[i], elems[j])] for j in range(n)] for i in range(n)]

def dihedral(m):
    mul = lambda a, b: ((a[0] + (1 if a[1] == 0 else -1) * b[0]) % m, (a[1] + b[1]) % 2)
    return mul, (0, 0), [(1, 0), (0, 1)]

def dicyclic(p):  # Z_p : Z_4 with inversion (order 4p)
    mul = lambda a, b: ((a[0] + (1 if a[1] % 2 == 0 else -1) * b[0]) % p, (a[1] + b[1]) % 4)
    return mul, (0, 0), [(1, 0), (0, 1)]

def perm_mul(p, q):  # apply q then p? use p∘q
    return tuple(p[i] for i in q)

def A5_times_Z(k):
    # A5 as perms of 5 points, times Z_k
    def mul(a, b):
        return (perm_mul(a[0], b[0]), (a[1] + b[1]) % k)
    gens = [((1, 2, 0, 3, 4), 0), ((1, 2, 3, 4, 0), 0), ((0, 1, 2, 3, 4), 1)]
    return mul, ((0,1,2,3,4), 0), gens

def A4_times_Z(k):
    def mul(a, b):
        return (perm_mul(a[0], b[0]), (a[1] + b[1]) % k)
    gens = [((1, 2, 0, 3), 0), ((1, 0, 3, 2), 0), ((1, 0, 2, 3), 0)]  # wrong? fixed below
    gens = [((1, 2, 0, 3), 0), ((1, 0, 3, 2), 0), ((0, 1, 2, 3), 1)]
    return mul, ((0,1,2,3), 0), gens

def D_times_Z(m, k):  # D_m x Z_k  (order 2m k)
    mul0, id0, gens0 = dihedral(m)
    mul = lambda a, b: (mul0(a[0], b[0]), (a[1] + b[1]) % k)
    gens = [(g, 0) for g in gens0] + [(id0, 1)]
    return mul, (id0, 0), gens

def get_group(name):
    if name.startswith("Dic"):         # Dic<p> order 4p
        mul, e, g = dicyclic(int(name[3:]))
    elif name == "A5xZ3":
        mul, e, g = A5_times_Z(3)
    elif name == "A4xZ15":
        mul, e, g = A4_times_Z(15)
    elif name.startswith("DxZ"):      # D<m>xZ<k>  (order 2mk)
        m, k = map(int, name[3:].split("_"))
        mul, e, g = D_times_Z(m, k)
    elif name.startswith("D"):         # D<m>  order 2m
        mul, e, g = dihedral(int(name[1:]))
    else:
        raise SystemExit("unknown group " + name)
    elems, idx = closure(g, mul, e)
    return elems, idx, mul

def main():
    name, mode = sys.argv[1], sys.argv[2]   # mode: grp | chein
    elems, idx, mul = get_group(name)
    m = len(elems)
    if mode == "grp":
        T = group_table(elems, idx, mul)
        n = m
    else:
        # Chein loop M(G,2): element (g,b) -> index 2*g+b
        inv = [None]*m
        for i, x in enumerate(elems):
            for j, y in enumerate(elems):
                if mul(x, y) == elems[0]:
                    inv[i] = j; break
        M = group_table(elems, idx, mul)
        n = 2*m
        T = [[0]*n for _ in range(n)]
        for g in range(m):
            for b1 in (0,1):
                for h in range(m):
                    for b2 in (0,1):
                        a = 2*g+b1; c = 2*h+b2
                        if b1 == 0 and b2 == 0: r, s = M[g][h], 0
                        elif b1 == 0 and b2 == 1: r, s = M[h][g], 1
                        elif b1 == 1 and b2 == 0: r, s = M[g][inv[h]], 1
                        else: r, s = M[inv[h]][g], 0
                        T[a][c] = 2*r+s
    # checks: identity-free latin square check
    ok = all(len(set(row)) == n for row in T) and all(len({T[i][j] for i in range(n)}) == n for j in range(n))
    tag = f"{name}_{mode}"
    path = os.path.join(OUT, tag + ".tab")
    with open(path, "w") as f:
        f.write(f"{n}\n")
        for row in T:
            f.write(" ".join(map(str, row)) + "\n")
    print(tag, "order", n, "latin", ok, "->", path)

main()

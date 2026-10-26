# c17: permutation-group tables (wreath products, imprimitive groups) for lift.
import sys, numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups as G

def cyc(points):
    """permutation (as list of images on range(n)) given as a cycle on the list `points`"""
    return points

def perm_from_cycles(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return p

def wreath(block, k, base_gens, top_gens):
    """G wr top: G acts on k blocks of size `block`; base_gens are perms on `block` points,
    top_gens are perms on k blocks (as lists of length k). Returns (n, gens)."""
    n = block * k
    gens = []
    for g in base_gens:  # apply g on block 0 only
        p = list(range(n))
        for i in range(block):
            p[i] = g[i]
        gens.append(p)
    for t in top_gens:  # block permutation
        p = list(range(n))
        for b in range(k):
            for i in range(block):
                p[b * block + i] = t[b] * block + i
        gens.append(p)
    return n, gens

def tab(name, n, gens):
    T = G.t_perm(n, gens)
    N = len(T)
    return name, N, T

def write(name, T):
    G.write_bin(T, f"/home/user/degree-diameter/research/squads/b48/r1/c17/tab/{name}.bin")

def prod(T1, T2):
    return G.t_prod(T1, T2)

def sym_top(k):
    # full symmetric group on k blocks: transposition and k-cycle
    tr = list(range(k)); tr[0], tr[1] = 1, 0
    cy = [(i + 1) % k for i in range(k)]
    return [tr, cy]

specs = {}
# 1. Z24 wr Z2 (1152): base cyclic 24 on each block, swap
def cyc_block(m):
    return [(i + 1) % m for i in range(m)]
def wr_cyclic(m, k):
    base = cyc_block(m)
    n, gens = wreath(m, k, [base], [[1, 0] + list(range(2, k))] if k == 2 else [])
    # second block generator
    p = list(range(n))
    for i in range(m):
        p[m + i] = m + base[i]
    gens.append(p)
    return n, gens
# Z_m wr Z_2 with base generator on each block and swap
def wr2(base_gen_list, m):
    n = 2 * m
    gens = []
    for g in base_gen_list:
        p = list(range(n))
        for i in range(m):
            p[i] = g[i]
        gens.append(p)
        q = list(range(n))
        for i in range(m):
            q[m + i] = m + g[i]
        gens.append(q)
    sw = list(range(n))
    for i in range(m):
        sw[i], sw[m + i] = m + i, i
    gens.append(sw)
    return n, gens

specs["Z24wrZ2"] = wr2([cyc_block(24)], 24)
specs["Z25wrZ2"] = wr2([cyc_block(25)], 25)
specs["D12wrZ2"] = wr2([cyc_block(12), [(-i) % 12 for i in range(12)]], 12)  # D12 on 12 points: rotation + reflection
specs["S4wrZ2"] = wr2([[1, 0, 2, 3], [1, 2, 3, 0]], 4)
specs["A4wrZ2"] = wr2([[1, 2, 0, 3], [1, 0, 3, 2]], 4)   # not exactly A4; checked by order below
specs["Z5wrZ2"] = wr2([cyc_block(5)], 5)

# S3 wr S3 (1296), degree 9
n = 9
g = []
for b in range(3):
    o = 3 * b
    p = list(range(n)); p[o], p[o + 1] = o + 1, o; g.append(p)
    p = list(range(n)); p[o], p[o + 1], p[o + 2] = o + 1, o + 2, o; g.append(p)
p = list(range(n)); [p.__setitem__(i, i + 3) or p.__setitem__(i + 3, i) for i in range(3)]; g.append(p)
p = list(range(n)); [p.__setitem__(i + 3, i + 6) or p.__setitem__(i + 6, i + 3) for i in range(3)]; g.append(p)
specs["S3wrS3"] = (9, g)

# Z3 wr Z5 (1215), degree 15
n = 15
g = []
for b in range(5):
    o = 3 * b
    p = list(range(n)); p[o], p[o + 1], p[o + 2] = o + 1, o + 2, o; g.append(p)
p = list(range(n))
for b in range(5):
    for i in range(3):
        p[3 * b + i] = 3 * ((b + 1) % 5) + i
g.append(p)
specs["Z3wrZ5"] = (15, g)

# Z4 wr Z3 (192) x Z6 = 1152 ; Z3 wr Z4 (324) x Z4 = 1296 handled as products below
n, g = wr2([[1, 2, 3, 0]], 4)  # placeholder (Z4 wr Z2), replaced below
specs["Z4wrZ2"] = (n, g)
n = 12; g = []
for b in range(3):
    o = 4 * b
    p = list(range(n)); p[o], p[o + 1], p[o + 2], p[o + 3] = o + 1, o + 2, o + 3, o; g.append(p)
p = list(range(n))
for b in range(3):
    for i in range(4):
        p[4 * b + i] = 4 * ((b + 1) % 3) + i
g.append(p)
specs["Z4wrZ3"] = (12, g)

# S3 wr Z2 (72), degree 6
n = 6; g = []
p = list(range(n)); p[0], p[1] = 1, 0; g.append(p)
p = list(range(n)); p[0], p[1], p[2] = 1, 2, 0; g.append(p)
p = list(range(n)); p[3], p[4] = 4, 3; g.append(p)
p = list(range(n)); p[3], p[4], p[5] = 4, 5, 3; g.append(p)
p = list(range(n)); [p.__setitem__(i, i + 3) or p.__setitem__(i + 3, i) for i in range(3)]; g.append(p)
specs["S3wrZ2"] = (6, g)

# S4 wr Z2 is above; B4 = Z2 wr S4 (384) on 8 points
n = 8; g = []
p = list(range(n)); p[0], p[1] = 1, 0; g.append(p)
p = list(range(n)); p[0], p[1], p[2], p[3] = 1, 2, 3, 0; g.append(p)  # placeholder cycles below
g = []
for blk in range(4):
    o = 2 * blk
    p = list(range(n)); p[o], p[o + 1] = o + 1, o; g.append(p)
p = list(range(n))
for i in range(4): p[2 * i], p[2 * i + 1] = 2 * ((i + 1) % 4), 2 * ((i + 1) % 4) + 1
g.append(p)
p = list(range(n)); p[0], p[2], p[4], p[6] = 2, 4, 6, 0; p[1], p[3], p[5], p[7] = 3, 5, 7, 1; g.append(p)
p = list(range(n)); p[0], p[2] = 2, 0; p[1], p[3] = 3, 1; g.append(p)
specs["B4"] = (8, g)

ORDER_OK = lambda N: 1094 <= N <= 1300
results = []
for name, (n, g) in specs.items():
    try:
        T = G.t_perm(n, g)
    except ValueError as e:
        print(name, "ERR", e); continue
    N = len(T)
    comm = bool(np.array_equal(T, T.T))
    print(f"{name}: degree {n} order {N} abelian={comm}", flush=True)

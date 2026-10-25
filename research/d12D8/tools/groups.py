"""Small finite groups as permutation groups -> (elements list, multiplication table with identity = 0)."""
import itertools, re

def closure(gens, n):
    idp = tuple(range(n))
    elems = [idp]; idx = {idp: 0}; frontier = [idp]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = tuple(g[x[i]] for i in range(n))  # y = g o x
                if y not in idx:
                    idx[y] = len(elems); elems.append(y); nf.append(y)
        frontier = nf
    return elems, idx

def table(elems, idx):
    m = len(elems)
    T = [[0] * m for _ in range(m)]
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            # product a*b as "apply b then a"? we use (a*b)(x) = a(b(x))
            c = tuple(a[b[k]] for k in range(len(a)))
            T[i][j] = idx[c]
    return T

def cyclic(m):
    g = tuple((i + 1) % m for i in range(m))
    return closure([g], m)

def direct(G1, G2):
    (e1, i1), (e2, i2) = G1, G2
    n1, n2 = len(e1[0]), len(e2[0])
    gens = []
    for x in e1[1:]:
        gens.append(tuple(list(x) + [n1 + y for y in range(n2)]))
    for y in e2[1:]:
        gens.append(tuple(list(range(n1)) + [n1 + yy for yy in y]))
    return closure(gens, n1 + n2)

def agl1(p):
    """AGL(1,p) acting on Z_p (p prime): x -> a x + b."""
    t = tuple((x + 1) % p for x in range(p))
    # generator of multiplicative group
    for g in range(2, p):
        if len({pow(g, k, p) for k in range(p - 1)}) == p - 1: break
    m = tuple((g * x) % p for x in range(p))
    return closure([t, m], p)

def frob(p, k):
    """Z_p x| Z_k with k | p-1 (subgroup of AGL(1,p))."""
    t = tuple((x + 1) % p for x in range(p))
    for g in range(2, p):
        if len({pow(g, j, p) for j in range(p - 1)}) == p - 1: break
    h = pow(g, (p - 1) // k, p)
    m = tuple((h * x) % p for x in range(p))
    return closure([t, m], p)

def dihedral(n):
    r = tuple((i + 1) % n for i in range(n)); s = tuple((-i) % n for i in range(n))
    return closure([r, s], n)

def sym(n):
    return closure([tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])], n)

def alt4():
    return closure([(1, 2, 0, 3), (0, 2, 3, 1)], 4)

def affine_f9_order4():
    """(Z3 x Z3) x| Z4, Z4 = <multiplication by i> on F9 = F3[i], i^2 = -1. Points of F9 indexed a+3b."""
    def idx(a, b): return (a % 3) + 3 * (b % 3)
    t1 = tuple(idx(a + 1, b) for b in range(3) for a in range(3))
    t2 = tuple(idx(a, b + 1) for b in range(3) for a in range(3))
    # multiply (a + b i) by i = -b + a i
    mi = tuple(idx(-b, a) for b in range(3) for a in range(3))
    return closure([t1, t2, mi], 9)

def by_name(name):
    if name == 'Z6xZ6': return direct(cyclic(6), cyclic(6))
    if re.fullmatch(r'Z\d+', name): return cyclic(int(name[1:]))
    if name.startswith('AGL'): return agl1(int(name[3:]))
    if name.startswith('D'): return dihedral(int(name[1:]))
    if name == 'A4xZ3': return direct(alt4(), cyclic(3))
    if name == 'S3xS3': return direct(sym(3), sym(3))
    if name == 'F9Z4': return affine_f9_order4()
    if name.startswith('Fr'):  # Fr13_3 etc
        p, k = name[2:].split('_'); return frob(int(p), int(k))
    if name == 'Z6xZ6': return direct(cyclic(6), cyclic(6))
    raise ValueError(name)

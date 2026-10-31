# Writes multiplication tables for small groups: file groups/<name>.txt
# format: line 1 = N; then N lines of N ints: row a, entry b = index of a*b. Identity is index 0.
import itertools, os, sys
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "groups")
os.makedirs(OUT, exist_ok=True)

def closure_perm(gens):
    n = len(gens[0]); idt = tuple(range(n))
    els = [idt]; seen = {idt}; i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = tuple(g[x[j]] for j in range(n))  # x then g (composition order irrelevant for a group table)
            if y not in seen: seen.add(y); els.append(y)
    return els

def table_from_elems(els, mulf):
    idx = {e: i for i, e in enumerate(els)}
    N = len(els)
    T = [[idx[mulf(els[a], els[b])] for b in range(N)] for a in range(N)]
    return T

def write(name, T):
    N = len(T)
    assert T[0] == list(range(N)), name
    with open(os.path.join(OUT, name + ".txt"), "w") as f:
        f.write(f"{N}\n")
        for row in T: f.write(" ".join(map(str, row)) + "\n")
    print(name, N)

def perm_group(name, gens, mulf=None):
    els = closure_perm(gens)
    if mulf is None: mulf = lambda x, y: tuple(x[y[j]] for j in range(len(x)))
    write(name, table_from_elems(els, mulf))

def cyclic(n): write(f"C{n}", [[(a + b) % n for b in range(n)] for a in range(n)])

def direct(name, mods):
    els = list(itertools.product(*[range(m) for m in mods]))
    els.sort(key=lambda t: (sum(1 for x in t if x), t))  # identity first
    mulf = lambda x, y: tuple((x[i] + y[i]) % mods[i] for i in range(len(mods)))
    write(name, table_from_elems(els, mulf))

def dihedral(n):  # D_n of order 2n, as permutations of Z_n: r: i->i+1, s: i->-i
    r = tuple((i + 1) % n for i in range(n)); s = tuple((-i) % n for i in range(n))
    perm_group(f"D{n}", [r, s])

def sym(n):
    gens = [tuple([1, 0] + list(range(2, n)))]
    gens.append(tuple(list(range(1, n)) + [0]))
    perm_group(f"S{n}", gens)

def alt(n):
    gens = [tuple([1, 2, 0] + list(range(3, n))), tuple([1, 0, 3, 2] + list(range(4, n))) if n >= 4 else None]
    gens = [g for g in gens if g]
    if n == 4:
        gens = [(1, 2, 0, 3), (1, 0, 3, 2)]
    perm_group(f"A{n}", gens)

def quaternion():
    # Q8 as signed units (sign, unit) with units 1,i,j,k
    tab = {('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
           ('i','1'):(1,'i'),('i','i'):(-1,'1'),('i','j'):(1,'k'),('i','k'):(-1,'j'),
           ('j','1'):(1,'j'),('j','i'):(-1,'k'),('j','j'):(-1,'1'),('j','k'):(1,'i'),
           ('k','1'):(1,'k'),('k','i'):(1,'j'),('k','j'):(-1,'i'),('k','k'):(-1,'1')}
    els = [(s, u) for s in (1, -1) for u in '1ijk']
    els.sort(key=lambda t: (t != (1, '1'), t))
    def mulf(x, y):
        s, u = tab[(x[1], y[1])]
        return (s * x[0] * y[0], u)
    write("Q8", table_from_elems(els, mulf))

def frobenius(p, q):  # C_p x| C_q (q | p-1) : x -> a x, y -> y + b ... built as affine maps on Z_p
    # elements (b, a): x -> a*x + b with a in subgroup of order q of Z_p^*
    gens_a = None
    for a in range(2, p):
        if pow(a, q, p) == 1 and all(pow(a, d, p) != 1 for d in range(1, q)):
            gens_a = a; break
    els = [(b, pow(gens_a, t, p)) for b in range(p) for t in range(q)]
    els.sort(key=lambda t: (t != (0, 1), t))
    def mulf(x, y):  # (x∘y)(z) = x(y(z)) : y(z)=a2 z + b2 ; x(...)=a1 a2 z + a1 b2 + b1
        b1, a1 = x; b2, a2 = y
        return ((a1 * b2 + b1) % p, (a1 * a2) % p)
    write(f"F{p}_{q}", table_from_elems(els, mulf))

if __name__ == "__main__":
    for n in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14): cyclic(n)
    direct("C2xC2", [2, 2]); direct("C2xC4", [2, 4]); direct("C2xC6", [2, 6]); direct("C3xC3", [3, 3])
    direct("C2xC2xC2", [2, 2, 2]); direct("C4xC4", [4, 4]); direct("C2xC8", [2, 8]); direct("C2xC2xC4", [2, 2, 4])
    dihedral(3); dihedral(4); dihedral(5); dihedral(6); dihedral(7); dihedral(8); dihedral(9)
    alt(4); quaternion(); frobenius(7, 3); frobenius(5, 2)
    # Dic3 = C3 x| C4 (order 12) and C3 x| C4 via perms
    perm_group("Dic3", [tuple([1, 2, 0, 4, 5, 3]), tuple([3, 4, 5, 0, 1, 2])]) if False else None

"""2^4 : A6 as an affine permutation group on 16 points: V = even subsets of {0..5} modulo complement (F_2^4),
A6 acts by permuting {0..5}, translations by V. Writes tabs/2^4A6.bin (order 5760)."""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import pgen, groups
FULL = 63
evens = [m for m in range(64) if bin(m).count("1") % 2 == 0]
classes = sorted({min(m, FULL ^ m) for m in evens})
assert len(classes) == 16
cidx = {c: i for i, c in enumerate(classes)}
def canon(m):
    return cidx[min(m, FULL ^ m)]
def apply_perm(sigma, m):          # sigma: list of images of 0..5
    r = 0
    for i in range(6):
        if m >> i & 1:
            r |= 1 << sigma[i]
    return r
def add_vec(a, b):                 # a, b are class indices -> symmetric difference of canonical reps
    return canon(classes[a] ^ classes[b])
gens = []
# translations by basis vectors: pick 4 classes that form a basis (use the class of {0,1},{0,2},{0,3},{0,4})
basis = [canon(0b000011), canon(0b000101), canon(0b001001), canon(0b010001)]
# check independence (16 elements generated)
span = {0}
for b in basis:
    span |= {add_vec(s, b) for s in span}
assert len(span) == 16, len(span)
for b in basis:
    gens.append(tuple(add_vec(p, b) for p in range(16)))
# A6 generators acting linearly
for sig in [(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)]:
    gens.append(tuple(canon(apply_perm(sig, classes[p])) for p in range(16)))
T = pgen.perm_table(gens)
N = len(T)
print("order", N)
groups.write_bin(T, os.path.join(HERE, "tabs", "2^4A6.bin"))

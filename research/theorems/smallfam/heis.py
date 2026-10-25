"""Explicit model of G = Heis(F_9) x| C_16, the group of the (4,7) graph on 864 vertices (SmallGroup(432,233)).

F_9 = F_3[i]/(i^2+1), v = a + b i.  omega(v, w) = Im(conj(v) w) = a b' - b a'  (conj = Frobenius v -> v^3).
Heis = F_9 x F_3 with (v, z)(w, z') = (v + w, z + z' + 2 omega(v, w))   (2 = 1/2 mod 3; exponent 3, centre 0 x F_3).
lambda = 1 + i has order 8 and norm lambda^4 = -1, so phi(v, z) = (lambda v, -z) is an automorphism of order 8.
G = Heis x| <y>, y of order 16 acting by phi:  (v, z, j)(w, z', l) = ((v, z) phi^j(w, z'), j + l).
Element index: ((a*3 + b)*3 + z)*16 + j.

Usage: python3 heis.py table OUT            write the multiplication table (hx/lx 'tab' format)
       python3 heis.py edges S1 S2 S3 S4 OUT   write the Haar graph edge list for S given as indices
       python3 heis.py show INDEX ...       print elements
"""
import sys

def fadd(v, w):
    return ((v[0] + w[0]) % 3, (v[1] + w[1]) % 3)

def fmul(v, w):          # (a + b i)(c + d i) = (ac - bd) + (ad + bc) i
    return ((v[0] * w[0] - v[1] * w[1]) % 3, (v[0] * w[1] + v[1] * w[0]) % 3)

def omega(v, w):
    return (v[0] * w[1] - v[1] * w[0]) % 3

LAM = (1, 1)
LPOW = [(1, 0)]
for _ in range(15):
    LPOW.append(fmul(LPOW[-1], LAM))
assert LPOW[8] == (1, 0) and LPOW[4] == (2, 0)

ELS = [((a, b), z, j) for a in range(3) for b in range(3) for z in range(3) for j in range(16)]
IDX = {e: n for n, e in enumerate(ELS)}
N = len(ELS)

def mul(x, y):
    (v, z, j), (w, zz, l) = x, y
    w2 = fmul(LPOW[j % 16], w)
    zz2 = zz if j % 2 == 0 else (-zz) % 3
    return (fadd(v, w2), (z + zz2 + 2 * omega(v, w2)) % 3, (j + l) % 16)

def check_group():
    e = ((0, 0), 0, 0)
    import random
    random.seed(1)
    for _ in range(3000):
        x, y, z = (random.choice(ELS) for _ in range(3))
        assert mul(mul(x, y), z) == mul(x, mul(y, z))
    assert all(mul(e, x) == x == mul(x, e) for x in ELS)

if __name__ == '__main__':
    check_group()
    cmd = sys.argv[1]
    if cmd == 'table':
        with open(sys.argv[2], 'w') as f:
            f.write(f'{N} {IDX[((0, 0), 0, 0)]}\n')
            for x in ELS:
                f.write(' '.join(str(IDX[mul(x, y)]) for y in ELS) + '\n')
    elif cmd == 'edges':
        S = [ELS[int(s)] for s in sys.argv[2:6]]
        with open(sys.argv[6], 'w') as f:
            f.write(f'{2 * N}\n')
            for g in ELS:
                for s in S:
                    f.write(f'{IDX[g]} {N + IDX[mul(s, g)]}\n')      # (g,A) ~ (s g, B)
        print('S =', S)
    elif cmd == 'show':
        for s in sys.argv[2:]:
            print(s, ELS[int(s)])

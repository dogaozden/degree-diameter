"""Heis(F_{p^2}) x| C_k for odd p: the family of the (4,7) graph (p = 3, k = 16, e = 1).

F_{p^2} = F_p[i]/(i^2 - n), n a non-residue mod p; v = a + b i.  omega(v, w) = a b' - b a'  (Im(conj(v) w) up to a
unit).  Heis = F_{p^2} x F_p with (v, z)(w, z') = (v + w, z + z' + omega(v, w)/2).  lambda = a primitive element of
F_{p^2}; phi(v, z) = (lambda^e v, N(lambda)^e z) with N(x) = x^(p+1) (omega(lambda v, lambda w) = N(lambda) omega(v,w)).
G = Heis x| <y>, y of order k acting by phi (needs phi^k = id).  Element (v, z, j), index ((a*p + b)*p + z)*k + j.
Usage: python3 heisq.py p k e OUT_TABLE      (writes the hx/hanneal table; prints the action order)
"""
import sys

p, k, e, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
n = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)      # non-residue


def fmul(v, w):
    return ((v[0] * w[0] + n * v[1] * w[1]) % p, (v[0] * w[1] + v[1] * w[0]) % p)


def fpow(v, t):
    r = (1, 0)
    for _ in range(t):
        r = fmul(r, v)
    return r


q = p * p
lam = None
for a in range(p):
    for b in range(p):
        v = (a, b)
        if v == (0, 0):
            continue
        x, o = v, 1
        while x != (1, 0):
            x = fmul(x, v)
            o += 1
        if o == q - 1:
            lam = v
            break
    if lam:
        break
L = fpow(lam, e)                 # lambda^e
Nl = fmul(L, fpow(L, p))[0]      # N(lambda^e) = (lambda^e)^(p+1), in F_p
order = 1
x = L
while not (x == (1, 0)):
    x = fmul(x, L)
    order += 1
assert k % order == 0, f'action order {order} does not divide k={k}'
LP = [(1, 0)]
for _ in range(k):
    LP.append(fmul(LP[-1], L))
NP = [pow(Nl, j, p) for j in range(k + 1)]
inv2 = (p + 1) // 2


def omega(v, w):
    return (v[0] * w[1] - v[1] * w[0]) % p


ELS = [((a, b), z, j) for a in range(p) for b in range(p) for z in range(p) for j in range(k)]
IDX = {el: t for t, el in enumerate(ELS)}


def mul(x, y):
    (v, z, j), (w, zz, l) = x, y
    w2 = fmul(LP[j], w)
    zz2 = NP[j] * zz % p
    return (((v[0] + w2[0]) % p, (v[1] + w2[1]) % p), (z + zz2 + inv2 * omega(v, w2)) % p, (j + l) % k)


N = len(ELS)
with open(out, 'w') as f:
    f.write(f'{N} {IDX[((0, 0), 0, 0)]}\n')
    for x in ELS:
        f.write(' '.join(str(IDX[mul(x, y)]) for y in ELS) + '\n')
print(f'Heis(F_{q}) x| C_{k}, lambda = {lam} (primitive), y acts by lambda^{e} (order {order}), N = {N}, n = {2 * N}')

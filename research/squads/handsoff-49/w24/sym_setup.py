"""w24: symmetric (Z_5-equivariant) voltage ansatz for the 5+5 base over meta:71:7:45.
Base sigma: diagonal 5-cycle i -> i+1 on both sides (preserves the missing matching A_i -- B_{i+1}); free on the 20 edges.
Group automorphisms phi of N = Z_71 x|_45 Z_7 (order 71*70 = 4970), found from generator images x=(1,0), y=(0,1).
Ansatz: volt(sigma e) = phi(volt(e)); the lift then has the automorphism (u,x) -> (sigma u, phi x).
Writes SYM_<k>.txt for each conjugacy class of order-5 phi (phi(x) = x^k): line 1 = K, line 2 = phi table,
line 3 = R (4 orbit reps), then per base edge: rep index and power p (volt_i = phi^p(g_rep))."""
import struct, array, random, sys
d = open('m497.bin', 'rb').read()
n = struct.unpack('i', d[:4])[0]
T = array.array('H'); T.frombytes(d[4:4 + 2 * n * n])
M, R = 71, 45
def mul(g, h): return T[g * n + h]
def idx(a, t): return a + M * t
def power(g, k):
    r = 0
    for _ in range(k): r = mul(r, g)
    return r
def order(g):
    k, h = 1, g
    while h != 0: h = mul(h, g); k += 1
    return k
x, y = idx(1, 0), idx(0, 1)
inv = [0] * n
for g in range(n):
    for h in range(n):
        if mul(g, h) == 0: inv[g] = h; break
xp_all = [idx(c, 0) for c in range(1, M)]
yp_all = [g for g in range(n) if g // M != 0 and order(g) == 7]
autos = []
for xp in xp_all:
    target = power(xp, R)
    for yp in yp_all:
        if mul(mul(yp, xp), inv[yp]) != target: continue
        phi = [mul(power(xp, g % M), power(yp, g // M)) for g in range(n)]
        autos.append((xp, yp, phi))
print('automorphisms found', len(autos))
# homomorphism spot check
for xp, yp, phi in autos[:50]:
    for _ in range(200):
        g, h = random.randrange(n), random.randrange(n)
        assert phi[mul(g, h)] == mul(phi[g], phi[h])
    assert len(set(phi)) == n
o5 = [(xp, yp, phi) for xp, yp, phi in autos if all(True for _ in [0])]
def phi_order(phi):
    k, cur = 1, phi[:]
    while cur != list(range(n)):
        cur = [phi[c] for c in cur]; k += 1
    return k
five = []
for xp, yp, phi in autos:
    if phi_order(phi) == 5: five.append((xp, yp, phi))
print('order-5 automorphisms', len(five))
# classes by phi(x) (conjugacy by automorphisms and the 71 translations gives the same linear part)
from collections import defaultdict
cls = defaultdict(list)
for xp, yp, phi in five: cls[xp].append((xp, yp, phi))
print('distinct phi(x) among order-5:', sorted(cls.keys())[:20], len(cls))
# base: edges of the 5+5 base
lines = open('q5.base').read().split('\n')
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
def sig(v, j=1):  # diagonal 5-cycle
    if v < 5: return (v + j) % 5
    return 5 + (v - 5 + j) % 5
def edge_index(u, v):
    for i, (a, c) in enumerate(E):
        if (a, c) == (u, v): return i
    raise KeyError
rep = [-1] * m; power_ = [0] * m; reps = []
for i in range(m):
    if rep[i] >= 0: continue
    r = len(reps); reps.append(i)
    u, v = E[i]
    for p in range(5):
        j = edge_index(sig(u, p), sig(v, p))
        assert rep[j] < 0
        rep[j] = r; power_[j] = p
assert len(reps) == 4, reps
written = []
for kk in sorted(cls.keys()):
    xp, yp, phi = cls[kk][0]
    fn = f'SYM_{kk}.txt'
    with open(fn, 'w') as f:
        f.write(f"{n}\n")
        f.write(' '.join(map(str, phi)) + '\n')
        f.write(f"{len(reps)}\n")
        for i in range(m): f.write(f"{rep[i]} {power_[i]}\n")
    written.append((kk, fn, len(cls[kk])))
print('written', written)

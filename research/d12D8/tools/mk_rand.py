"""hexagon H(q) + k random hop matchings; voltages in Z_N.
mode 'rand': all voltages uniform random; 'lev': Z_(2k+1) levels x Z_(N/(2k+1)) with random second component (CRT, needs gcd=1);
mode 'hop': hexagon voltage 0, hop voltages uniform random."""
import sys, random
from math import gcd
from hexlib import load_hex, write_base
q, k, N, mode, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]), sys.argv[6]
random.seed(seed)
n, lines = load_hex(q)
L = 2 * k + 1
def crt(a, b):  # element of Z_N with a mod L, b mod N/L
    m2 = N // L
    for x in range(N):
        if x % L == a % L and x % m2 == b % m2: return x
E = []
for l in range(n):
    for p in lines[l]:
        if mode == 'rand': g = random.randrange(N)
        elif mode == 'lev': g = crt(0, random.randrange(N // L))
        else: g = 0
        E.append((int(p), l, g))
for j in range(1, k + 1):
    perm = list(range(n)); random.shuffle(perm)
    for p in range(n):
        if mode == 'rand' or mode == 'hop': g = random.randrange(N)
        else: g = crt(j, random.randrange(N // L))
        E.append((p, perm[p], g))
write_base(out, n, E, N)

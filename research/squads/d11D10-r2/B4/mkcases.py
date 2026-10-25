#!/usr/bin/env python3
"""B4 helper: GF(243) = GF(3)[x]/(x^5+2x+1) arithmetic, random det-1 generators, corrupted copies.

Usage (run with -I):
  python3 -I mkcases.py big OUT.txt SEED            # 11 random generators over psl 243 x Z_11, header D=10
  python3 -I mkcases.py repeat IN.txt OUT.txt       # generator 7 replaced by a copy of generator 3
  python3 -I mkcases.py change IN.txt OUT.txt SEED  # generator 5 replaced by a random SL(2,243) element (z=0)
  python3 -I mkcases.py breakdet IN.txt OUT.txt     # generator 5: one entry changed so that det != 1
Field elements are integers sum c_i 3^i (c_i = coefficient of x^i), as haar_sym writes them.
"""
import random
import sys

P, E = 3, 5
Q = P ** E  # 243
# x^5 = -2x - 1 = x + 2 (mod 3)


def digits(a):
    return [(a // P ** i) % P for i in range(E)]


def from_digits(c):
    return sum(c[i] * P ** i for i in range(E))


def fadd(a, b):
    return from_digits([(x + y) % P for x, y in zip(digits(a), digits(b))])


def fneg(a):
    return from_digits([(-x) % P for x in digits(a)])


def fmul(a, b):
    A, B = digits(a), digits(b)
    pr = [0] * (2 * E - 1)
    for i in range(E):
        for j in range(E):
            pr[i + j] = (pr[i + j] + A[i] * B[j]) % P
    for i in range(2 * E - 2, E - 1, -1):      # reduce x^i, i >= 5, using x^5 = -2x - 1
        t = pr[i]
        if t:
            pr[i] = 0
            pr[i - 4] = (pr[i - 4] - 2 * t) % P  # x^i = x^(i-5) * (-2x - 1): the -2x term
            pr[i - 5] = (pr[i - 5] - t) % P      # the -1 term
    return from_digits(pr[:E])


INV = [0] * Q
for a in range(1, Q):
    for b in range(1, Q):
        if fmul(a, b) == 1:
            INV[a] = b
            break
for a in range(1, Q):
    assert fmul(a, INV[a]) == 1
# field axioms spot check: distributivity and associativity on a sample
rng0 = random.Random(1)
for _ in range(2000):
    a, b, c = (rng0.randrange(Q) for _ in range(3))
    assert fmul(a, fadd(b, c)) == fadd(fmul(a, b), fmul(a, c))
    assert fmul(fmul(a, b), c) == fmul(a, fmul(b, c))


def rand_sl(rng):
    a = rng.randrange(1, Q)
    b = rng.randrange(Q)
    c = rng.randrange(Q)
    d = fmul(fadd(1, fmul(b, c)), INV[a])  # a d - b c = 1
    assert fadd(fmul(a, d), fneg(fmul(b, c))) == 1
    return a, b, c, d


HDR_TAIL = "psl 243 poly x^5+2x+1"


def gen_line(i, m, z):
    return "%d mat(%d,%d,%d,%d) z=%d" % (i, m[0], m[1], m[2], m[3], z)


def read_gens(path):
    with open(path) as f:
        lines = f.read().splitlines()
    head = lines[0]
    gens = lines[1:]
    return head, gens


def parse_gen(line):
    import re
    m = re.search(r"mat\((\d+),(\d+),(\d+),(\d+)\)", line)
    z = re.search(r"z=(\d+)", line)
    return tuple(int(x) for x in m.groups()), int(z.group(1))


def main():
    mode = sys.argv[1]
    if mode == "big":
        out, seed = sys.argv[2], int(sys.argv[3])
        rng = random.Random(seed)
        n = 11
        gens = [((1, 0, 0, 1), 0)]  # s_0 = e
        while len(gens) < 11:
            gens.append((rand_sl(rng), rng.randrange(n)))
        head = "11 10 %s n %d N %d" % (HDR_TAIL, n, Q * (Q * Q - 1) // 2 * n)
    else:
        inp, out = sys.argv[2], sys.argv[3]
        head, lines = read_gens(inp)
        gl = [parse_gen(l) for l in lines]
        rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
        if mode == "repeat":
            gl[7] = gl[3]
        elif mode == "change":
            m = rand_sl(rng)
            while m == gl[5][0]:
                m = rand_sl(rng)
            gl[5] = (m, 0)
        elif mode == "breakdet":
            (a, b, c, d), z = gl[5]
            m2 = (a, b, c, fadd(d, 1)) if a != 0 else (fadd(a, 1), b, c, d)  # det becomes 1 + a or 1 + d... != 1
            assert fadd(fmul(m2[0], m2[3]), fneg(fmul(m2[1], m2[2]))) != 1
            gl[5] = (m2, z)
        else:
            raise SystemExit("unknown mode")
        gens = gl
    with open(out, "w") as f:
        if mode == "big":
            f.write(head + "\n")
        else:
            f.write(head + "\n")
        for i, (m, z) in enumerate(gens):
            f.write(gen_line(i, m, z) + "\n")
    print("wrote", out, "generators", len(gens))


if __name__ == "__main__":
    main()

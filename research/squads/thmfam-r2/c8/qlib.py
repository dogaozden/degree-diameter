# Independent arithmetic for the card c8 audit of HAAR_FAMILIES.md (no lab code used).
import math
from collections import deque

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def primes(lo, hi):
    return [n for n in range(lo, hi + 1) if is_prime(n)]

# Hamilton quaternions with integer coordinates (a0, a1, a2, a3) = a0 + a1 i + a2 j + a3 k
def qmul(a, b):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return (a0*b0 - a1*b1 - a2*b2 - a3*b3,
            a0*b1 + a1*b0 + a2*b3 - a3*b2,
            a0*b2 - a1*b3 + a2*b0 + a3*b1,
            a0*b3 + a1*b2 - a2*b1 + a3*b0)

def qconj(a):
    return (a[0], -a[1], -a[2], -a[3])

def qnorm(a):
    return sum(t * t for t in a)

def psi(al, x, y, q):
    """The displayed formula of Definition 2.2, typed literally."""
    a0, a1, a2, a3 = al
    return tuple(t % q for t in (a0 + a1*x + a3*y, -a1*y + a2 + a3*x,
                                 -a1*y - a2 + a3*x, a0 - a1*x - a3*y))

def mm(A, B, q):
    a, b, c, d = A; e, f, g, h = B
    return ((a*e + b*g) % q, (a*f + b*h) % q, (c*e + d*g) % q, (c*f + d*h) % q)

def madj(A, q):
    a, b, c, d = A
    return (d % q, (-b) % q, (-c) % q, a % q)

def mdet(A, q):
    return (A[0]*A[3] - A[1]*A[2]) % q

def minv(A, q):
    d = mdet(A, q)
    assert d
    t = pow(d, q - 2, q)
    return tuple(x * t % q for x in madj(A, q))

def pnorm(A, q):
    """Projective normal form: scale so that the first nonzero entry is 1."""
    A = tuple(x % q for x in A)
    for x in A:
        if x:
            t = pow(x, q - 2, q)
            return tuple(y * t % q for y in A)
    raise ValueError("zero matrix")

def is_square_mod(a, q):
    a %= q
    return a != 0 and pow(a, (q - 1) // 2, q) == 1

def lps_set(p):
    """Definition 2.1, typed literally."""
    R = math.isqrt(p)
    S = []
    for a0 in range(-R, R + 1):
        for a1 in range(-R, R + 1):
            for a2 in range(-R, R + 1):
                for a3 in range(-R, R + 1):
                    al = (a0, a1, a2, a3)
                    if qnorm(al) != p:
                        continue
                    if p % 4 == 1:
                        ok = a0 > 0 and a0 % 2 == 1 and a1 % 2 == 0 and a2 % 2 == 0 and a3 % 2 == 0
                    else:
                        ok = (a0 % 2 == 0 and a1 % 2 == 1 and a2 % 2 == 1 and a3 % 2 == 1
                              and (a0 > 0 or (a0 == 0 and a1 > 0)))
                    if ok:
                        S.append(al)
    return S

def xy_solutions(q):
    return [(x, y) for x in range(q) for y in range(q) if (x*x + y*y + 1) % q == 0]

def sigma(al):
    a0, a1, a2, a3 = al
    return (a0, a3, a1, a2)   # a0 + a3 i + a1 j + a2 k

def haar_component(Sm, q, start=None):
    """Component of (I,A) in H(PGL(2,q), Sm): (g,A) ~ (M g,B), (g,B) ~ (adj(M) g, A).
    Returns dict vertex -> distance, vertex = (pnorm(g), 'A'|'B')."""
    I = pnorm((1, 0, 0, 1), q)
    s = (I, 'A') if start is None else start
    dist = {s: 0}
    dq = deque([s])
    adjs = [madj(M, q) for M in Sm]
    while dq:
        v = dq.popleft()
        g, side = v
        if side == 'A':
            nxt = [(pnorm(mm(M, g, q), q), 'B') for M in Sm]
        else:
            nxt = [(pnorm(mm(Mi, g, q), q), 'A') for Mi in adjs]
        for w in nxt:
            if w not in dist:
                dist[w] = dist[v] + 1
                dq.append(w)
    return dist

def ecc(dist):
    return max(dist.values())

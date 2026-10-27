#!/usr/bin/env python3
"""Card c2: integer-lift family, Delta = 7, type 1+3+3 (psl).

S = {F} u O(X) u O(Y), F in {I, w, w2} (w = [[0,-1],[1,-1]], order 3 over Z), O(X) = {X, w X w^-1, w^2 X w^-2}.
X, Y are integer matrices of det 1 (computed over Z, then reduced mod q).

Usage: gen_c2.py q m F X Y
   F = I | w | w2 ;  X, Y = "a,b,c,d" (integer entries, det 1)
   m is ignored (psl, m = 1).
Prints 7 lines "a b c d 0".  Exits 1 with a message on stderr if the 7 elements are not distinct in PSL(2,q).
"""
import sys

W = (0, -1, 1, -1)       # w, det 1, w^3 = I over Z
WI = (-1, 1, -1, 0)      # w^-1 = w^2
LETTERS = {'I': (1, 0, 0, 1), 'w': W, 'w2': WI}


def mul(X, Y):
    a, b, c, d = X
    e, g, h, i = Y
    return (a * e + b * h, a * g + b * i, c * e + d * h, c * g + d * i)


def orbit(X):
    """O(X) over Z, in order (X, wXw^-1, w^2 X w^-2)."""
    return [X, mul(mul(W, X), WI), mul(mul(WI, X), W)]


def det(X):
    a, b, c, d = X
    return a * d - b * c


def psl_key(X, q):
    """Key of X mod q up to sign (PSL(2,q) element)."""
    Y = tuple(t % q for t in X)
    neg = tuple((-t) % q for t in Y)
    return min(Y, neg)


def family_lines(q, F, X, Y):
    """Return the 7 generators (mod q) or raise ValueError if not 7 distinct PSL elements."""
    if det(X) != 1 or det(Y) != 1:
        raise ValueError('X and Y must have determinant 1')
    S = [LETTERS[F]] + orbit(X) + orbit(Y)
    keys = [psl_key(Z, q) for Z in S]
    if len(set(keys)) != len(keys):
        raise ValueError('elements not distinct in PSL(2,%d)' % q)
    return [tuple(t % q for t in Z) for Z in S]


def parse_matrix(s):
    v = tuple(int(t) for t in s.split(','))
    if len(v) != 4:
        raise ValueError('matrix needs 4 entries: ' + s)
    return v


def main():
    if len(sys.argv) != 6:
        sys.stderr.write('usage: gen_c2.py q m F X Y\n')
        return 2
    q = int(sys.argv[1])
    F = sys.argv[3]
    if F not in LETTERS:
        sys.stderr.write('F must be I, w or w2\n')
        return 2
    try:
        lines = family_lines(q, F, parse_matrix(sys.argv[4]), parse_matrix(sys.argv[5]))
    except ValueError as e:
        sys.stderr.write(str(e) + '\n')
        return 1
    for Z in lines:
        print(*Z, 0)
    return 0


if __name__ == '__main__':
    sys.exit(main())

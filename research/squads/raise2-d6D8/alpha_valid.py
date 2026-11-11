"""List conjugating elements x of SL(2,q) (as printed by haar_sym 'alpha: conj by mat(a,b,c,d) (index i)') with x^k = +-I.
usage: python3 alpha_valid.py Q k IDX_FILE   (IDX_FILE: lines 'i a b c d' produced from haar_sym ALPHA=i RANDORB=1 output)"""
import sys
q, k = int(sys.argv[1]), int(sys.argv[2])
def mul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return ((a*e+b*g) % q, (a*f+b*h) % q, (c*e+d*g) % q, (c*f+d*h) % q)
for line in open(sys.argv[3]):
    p = line.split()
    if len(p) != 5: continue
    i, x = int(p[0]), tuple(int(v) for v in p[1:])
    y = (1, 0, 0, 1)
    for _ in range(k): y = mul(y, x)
    I, mI = (1, 0, 0, 1), (q-1, 0, 0, q-1)
    if y in (I, mI) and x not in (I, mI):   # conj by x has order k in PSL
        print(i, *x)

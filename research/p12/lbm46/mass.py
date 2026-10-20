import sys, math
from fractions import Fraction
# usage: mass.py DELTA G TOTAL_MATRICES  < analysis stdout
d, g, tot = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
B = d-1; D = g//2-1
nonleaf = sum(B**l for l in range(0, D))   # root + levels 1..D-1
auttree = math.factorial(B)**(2*nonleaf)
s = Fraction(0)
for line in sys.stdin:
    if line.startswith('A\t'):
        _, a, c, e = line.split('\t'); s += Fraction(2*int(e)*auttree, int(a))
print('sum over graphs of 2*E_M*|Aut+ T|/|Aut G| =', s, ' expected', tot, ' OK' if s == tot else ' MISMATCH')

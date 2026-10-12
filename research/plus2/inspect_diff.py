import json, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from al import al_named
import lib
from diff_al import FILES, ROOT, norm
q = int(sys.argv[1])
n0, e0, names, F = al_named(q)
assert (n0, e0) == lib.araujo_lopez_graph(q)
n1, e1 = json.load(open(ROOT + FILES[q]))['output']
names[n0] = 'NEW0'; names[n0 + 1] = 'NEW1'
A, B = norm(e0), norm(e1)
side = {}
for u, v in e0:
    side[u] = 'P'; side[v] = 'L'
def nm(x): return names[x]
print('removed:')
for u, v in sorted(A - B): print('  ', nm(u), nm(v))
print('added:')
for u, v in sorted(B - A): print('  ', nm(u), nm(v))

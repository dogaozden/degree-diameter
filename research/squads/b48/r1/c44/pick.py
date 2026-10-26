import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r1/c44')
from mk import *
Qname, m = sys.argv[1], int(sys.argv[2])
QT, _ = build_Q(Qname); gens = find_gens(QT)
H = sorted(homs(m, QT, gens))
nontriv = [k for k, p in enumerate(H) if any(x != 1 for x in p)]
print(Qname, m, 'homs', [ [p[g] for g in gens] for p in H ], 'nontrivial idx', nontriv)

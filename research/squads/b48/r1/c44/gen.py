import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r1/c44')
from mk import *
Qname, m, k, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
QT, _ = build_Q(Qname); gens = find_gens(QT)
H = sorted(homs(m, QT, gens)); phi = H[k]
T = semidirect(m, QT, phi); check_group(T); write_bin(T, out)
print(out, 'N=', T.shape[0], 'Q=', Qname, 'm=', m, 'phi_gens=', [phi[g] for g in gens])

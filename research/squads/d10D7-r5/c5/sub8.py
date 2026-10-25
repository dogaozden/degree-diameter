# c5: orbit-clique over subgroups of Sp_6(2) (embedded in Sp_6(8)) on PG(5,8): O^+_6(2)=S_8 (reflections t_v, Q(v)=1), O^-_6(2).
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from torus8 import *
def Qplus(v): return (v[0]*v[3] + v[1]*v[4] + v[2]*v[5]) % 2
def Qminus(v): return (v[0]*v[3] + v[1]*v[4] + v[2]*v[5] + v[0]*v[1] + v[3]*v[4]) % 2
def refl(v):  # t_v over GF(2): x -> x + B(x,v) v, matrix I + v (Jv)^T
    return (np.eye(6, dtype=np.int64) + np.outer(v, (v @ J6) % 2)) % 2
def group_gens(Qf):
    vs = [np.array([(c >> i) & 1 for i in range(6)]) for c in range(1, 64)]
    return [refl(v) for v in vs if Qf(v) == 1]
for name, Qf in [('O+6(2)', Qplus), ('O-6(2)', Qminus)]:
    gens = group_gens(Qf)
    print(name, 'number of generating reflections', len(gens), flush=True)
    res = run(gens, name, tlimit=120)
    if res:
        ids = to_hex_ids(np.array(res))
        print(name, 'size', len(ids), flush=True)
        np.savetxt('/home/user/degree-diameter/research/squads/d10D7-r5/c5/best_%s.txt' % name.replace('+', 'p').replace('-', 'm'), ids, fmt='%d')

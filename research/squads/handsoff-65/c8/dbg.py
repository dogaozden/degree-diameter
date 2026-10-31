import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from g2grp import *
from lin import preserves_phi
import random
random.seed(2)
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
u = unip(E[0])
print("single phi", preserves_phi(u))
from lin import Bbasis
_pos={};_c=0
for _i in range(N):
    for _j in range(_i,N):
        _pos[(_i,_j)]=_c;_c+=1
B=[[Bbasis[0][_pos[(min(i,j),max(i,j))]] for j in range(N)] for i in range(N)]
def Bform(x, y): return sum(x[i]*B[i][j]*y[j] for i in range(N) for j in range(N)) % p
v = allpts[5]
w = [sum(u[r][c]*v[c] for c in range(N)) % p for r in range(N)]
print("Q(v)", Bform(v, v), "Q(uv)", Bform(w, w))
g = mat_mul(unip(E[1]), unip(E[2]))
print("product phi", preserves_phi(g))

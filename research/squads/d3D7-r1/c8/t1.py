import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/d3D7-r1/c8')
from alg import *
# Wenger-type test: k=4 over GF(3): l_i + p_i = p1*l_{i-1}  (i=2..4)
fs=[{(('p',1),('l',i-1)):1} for i in range(2,5)]
r=build([3,3,3,3],fs); print(r[0], score(*r))
fs=[{(('p',1),('l',1)):1},{(('p',2),('l',1)):1,(('p',1),('l',2)):1},{(('p',1),('l',3)):1,(('p',3),('l',1)):1}]
r=build([3,3,3,3],fs); print(r[0], score(*r))

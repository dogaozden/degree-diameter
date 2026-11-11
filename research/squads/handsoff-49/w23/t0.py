import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
t=time.time()
TP, C = abelian_P([5,5,5,5])
A = [[2,0,0,0],[0,2,0,0],[0,0,2,0],[0,0,0,2]]
TPp, phi = abelian_auto([5,5,5,5], A)
check_automorphism(TPp, phi)
T = semidirect(TPp, phi)
GR.check(T)
write_bin(T, 'tabs/z5_4_s2.bin')
print('built', time.time()-t)
t=time.time()
print(invariants(T), time.time()-t)

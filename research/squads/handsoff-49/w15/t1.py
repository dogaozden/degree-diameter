import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
# Z_625 x| Z_4 with t: x -> 182 x (metacyclic, order 4 mod 625)
TP, C = abelian_P([625])
TPp, phi = abelian_auto([625], [[182]])
check_automorphism(TPp, phi)
T = semidirect(TPp, phi)
write_bin(T, 'tabs/z625_182.bin')
print(invariants(T))

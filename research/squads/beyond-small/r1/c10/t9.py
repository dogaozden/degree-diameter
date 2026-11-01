import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/beyond-small/r1/c10')
sys.path.insert(0,"/home/user/degree-diameter/research/squads/beyond-small/r1/c10"); from mzgrp import *
G = Grp(69, 22, 8, 22, 1)
print("valid", valid(69,22,8,22,1))
S = [(0,0),(66,11),(56,11),(28,13),(22,9),(13,15),(64,7),(25,14),(8,8)]
S = [i*22+j for (i,j) in S]
print("XX uncovered", XX_uncovered(G,S))
print("beta-psi closed:", all(G.psi(s) in S for s in S))
print("diam, connected", haar_edges_ok(G,S))

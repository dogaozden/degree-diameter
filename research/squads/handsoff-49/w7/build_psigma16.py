"""PSigmaL(2,16) = PSL(2,16) : <Frobenius x -> x^4> acting on the 17 points of PG(1,16). Writes tabs/PSigmaL2_16.bin."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import numpy as np
import pgen, groups
p, k, poly = 2, 4, [1, 1, 0, 0]          # GF(16), x^4 = x + 1
q, MUL, ADD, INV, NEG = pgen.gf_tables(p, k, poly)
gens = pgen.pl_gens(p, k, poly, False)
frob = [MUL[MUL[x][x]][MUL[x][x]] if x < q else x for x in range(q)]   # x -> x^4
sigma = tuple([frob[x] for x in range(q)] + [q])                      # infinity fixed
gens = [tuple(g) for g in gens] + [sigma]
T = pgen.perm_table(gens)
N = len(T)
groups.write_bin(T, os.path.join(os.path.dirname(os.path.abspath(__file__)), "tabs", "PSigmaL2_16.bin"))
print("PSigmaL2_16", N)

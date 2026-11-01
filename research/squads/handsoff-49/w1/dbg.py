import numpy as np, sys
sys.path.insert(0, '.')
from cov import load, inv_table, cost, ball_uncov
T = load('tabs/A7.bin'); N = len(T); I = inv_table(T)
S = [0, 972, 347, 630]
U = {int(T[I[t], s]) for s in S for t in S}
V = {int(T[s, I[t]]) for s in S for t in S}
print("|U|", len(U), "|V|", len(V), "T[0,0]", T[0,0], "I[5]*5", T[I[5],5])
# brute force ball
def ball(gens, k):
    B = {0}; fr = {0}
    for _ in range(k):
        nf = {int(T[g, x]) for g in gens for x in fr}
        fr = nf - B; B |= nf
    return B
for name, G in (("U", U), ("V", V)):
    gens = [g for g in G if g != 0]
    B = ball(gens, 4)
    print(name, "ball4 size", len(B), "uncov", N - len(B), "ball2", len(ball(gens, 2)), "ball3", len(ball(gens, 3)))
print(cost(T, I, S))
# check the group: is the table a group? associativity sample
import random
for _ in range(5):
    a, b, c = [random.randrange(N) for _ in range(3)]
    assert T[T[a, b], c] == T[a, T[b, c]]
print("assoc ok; order of 972:", [k for k in range(1, 8) if np.all(np.arange(1)==0) and False] )

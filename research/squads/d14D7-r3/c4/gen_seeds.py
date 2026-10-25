# gen_seeds.py SEED K OUTPREFIX: elliptic sections {a,b}^perp cap E (a,b non-orthogonal points of E).
# Each set S = common neighbours of a,b in the collinearity graph of Q^-(5,11) = points of E in the 4-space K^perp,
# K = <a,b> hyperbolic. S is a partial ovoid of size q^2+1 = 122 (pairwise non-orthogonal). Writes OUTPREFIX_k.txt
# (hexagon point ids, column 1 of E11.map), and OUTPREFIX_union.txt = S_1 followed by S_2 (combination seed).
import random, sys
q = 11
E = []
for line in open('/home/user/degree-diameter/research/cell147/data/E11.map'):
    t = list(map(int, line.split()))
    E.append((t[0], t[2:9]))
def Bf(x, y):
    s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]
    return s % q
random.seed(int(sys.argv[1])); K = int(sys.argv[2]); pref = sys.argv[3]
n = len(E); secs = []
while len(secs) < K:
    a = random.randrange(n); b = random.randrange(n)
    if Bf(E[a][1], E[b][1]) == 0: continue
    S = [i for i in range(n) if Bf(E[i][1], E[a][1]) == 0 and Bf(E[i][1], E[b][1]) == 0]
    ok = len(S) == q*q + 1 and all(Bf(E[i][1], E[j][1]) != 0 for i in S for j in S if i < j)
    if not ok: print("not a partial ovoid", len(S)); continue
    secs.append(S)
    with open('%s_%d.txt' % (pref, len(secs)), 'w') as f:
        f.write('\n'.join(str(E[i][0]) for i in S) + '\n')
    print("section", len(secs), "a=", E[a][0], "b=", E[b][0], "size", len(S))
if len(secs) >= 2:
    with open('%s_union.txt' % pref, 'w') as f:
        f.write('\n'.join(str(E[i][0]) for S in secs[:2] for i in S) + '\n')

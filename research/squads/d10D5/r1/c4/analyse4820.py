import sys, time
sys.path.insert(0, '.')
from pflag import *
rows = {}
for ln in open('../../hubs/graphs/d10D5_n4820_gqdm_flags5.sol'):
    t = ln.split()
    if t: rows[t[0]] = t[1:]
free = list(map(int, rows['free'])); sig = list(map(int, rows['sigma']))
flags = [(p, sig[p]) for p in free]
print('flags', flags)
pm = matching(flags); print('matching size', pm[0], 'of', N)
patch, commA, commB, coll, conc, NEED1, NEED2 = relations(flags)
k = len(flags)
print('collinear pairs', [(i, j) for i in range(k) for j in range(i) if coll[i][j]])
print('concurrent pairs', [(i, j) for i in range(k) for j in range(i) if conc[i][j]])
print('NEED1', [(i, j) for i in range(k) for j in range(k) if NEED1[i][j]])
print('NEED2', [(i, j) for i in range(k) for j in range(k) if NEED2[i][j]])
print('patch R(x,y)', [(x, y) for x in range(k) for y in range(k) if patch[x][y]])
print('commA (line-hub pairs)', commA, 'commB (point-hub pairs)', commB)
hg = list(map(int, rows['hubgraph']))
E = [(hg[e], hg[e + 1]) for e in range(0, len(hg), 2)]
print('existing hub-hub edges (a=L hub, b=P hub):', len(E))
Bex = {}
for a, b in E: Bex[(a, b)] = 1
miss = [(x, y) for x in range(k) for y in range(k) if patch[x][y] and not any(Bex.get((x*H+s, y*H+t)) for s in range(H) for t in range(H))]
print('patch requirements not met by 4820 hub graph:', miss)

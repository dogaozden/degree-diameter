# mkE9.py: elliptic section E = {X4 + C X0 = 0} of H(9) (GF(9) as in spreadpack9.c), with spread line ids.
# Output E9.map: one line per point of E: "pid spreadline x0 .. x6" (vertex index = line number).
import sys
ADD = [[0]*9 for _ in range(9)]; MUL = [[0]*9 for _ in range(9)]
for x in range(9):
    for y in range(9):
        a, b = x % 3, x // 3; c, d = y % 3, y // 3
        ADD[x][y] = (a + c) % 3 + 3*((b + d) % 3)
        re = (a*c + 2*b*d) % 3; im = (a*d + b*c) % 3
        MUL[x][y] = re + 3*im
NEG = [0]*9; INV = [0]*9
for x in range(9):
    for y in range(9):
        if ADD[x][y] == 0: NEG[x] = y
        if MUL[x][y] == 1: INV[x] = y
C = int(sys.argv[1]) if len(sys.argv) > 1 else 8
D = '/home/user/degree-diameter/research'
with open(D + '/cell147/data/gh_9.txt') as f:
    P, q = map(int, f.readline().split())
    lines = [list(map(int, f.readline().split())) for _ in range(P)]
with open(D + '/squads/d14D7-r3/c6/coords9.txt') as f:
    X = [list(map(int, f.readline().split())) for _ in range(P)]
inE = [ADD[X[p][4]][MUL[C][X[p][0]]] == 0 for p in range(P)]
spread = [-1]*P; nS = 0
for l in range(P):
    if all(inE[p] for p in lines[l]):
        nS += 1
        for p in lines[l]:
            assert spread[p] < 0
            spread[p] = l
Ep = [p for p in range(P) if inE[p]]
assert all(spread[p] >= 0 for p in Ep), 'E not covered by the spread'
with open('E9.map', 'w') as f:
    for p in Ep:
        f.write('%d %d %s\n' % (p, spread[p], ' '.join(map(str, X[p]))))
print('C=%d E points %d spread lines %d (q=%d)' % (C, len(Ep), nS, q))

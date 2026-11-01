import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
out = []
def perm_str(images):
    return ",".join(str(x) for x in images)
def spec(n, gens, extra=""):
    return "perm %d " % n + " ; ".join(perm_str(g) for g in gens)
# F_3^2 affine / linear maps, points a + 3b
p = 3
pts = [(a, b) for b in range(p) for a in range(p)]
idx = {v: i for i, v in enumerate(pts)}
def lin(M):
    return [idx[((M[0][0]*x + M[0][1]*y) % p, (M[1][0]*x + M[1][1]*y) % p)] for (x, y) in pts]
def trans(t):
    return [idx[((x + t[0]) % p, (y + t[1]) % p)] for (x, y) in pts]
T1, T2 = trans((1, 0)), trans((0, 1))
Q_i = [[0, 2], [1, 0]]; Q_j = [[1, 1], [1, 2]]
GL_extra = [[1, 0], [0, 2]]
out.append(("GL23", spec(9, [lin(Q_i), lin(Q_j), lin(GL_extra)]), 48))
out.append(("Z3^2:Q8", spec(9, [T1, T2, lin(Q_i), lin(Q_j)]), 72))
out.append(("Z3^2:SL23", spec(9, [T1, T2, lin([[1,1],[0,1]]), lin(Q_i), lin(Q_j)]), 216))
# AGL(1,9) and AGammaL(1,9) on F_9 = F_3[i], i^2=-1
F9 = [(a, b) for b in range(3) for a in range(3)]
id9 = {v: i for i, v in enumerate(F9)}
def mulg(v):  # times (1+i)
    a, b = v; return ((a - b) % 3, (a + b) % 3)
def frob(v):
    a, b = v; return (a, (-b) % 3)
def addt(t):
    return lambda v: ((v[0] + t[0]) % 3, (v[1] + t[1]) % 3)
def permof(f):
    return [id9[f(v)] for v in F9]
A9 = [permof(addt((1, 0))), permof(addt((0, 1))), permof(mulg)]
out.append(("AGL1-9", spec(9, A9), 72))
out.append(("AGaL1-9", spec(9, A9 + [permof(frob)]), 144))
# AGL(1,8) on F_8 = F_2[x]/(x^3+x+1), ints 0..7
def m8(v):
    v <<= 1
    if v & 8: v ^= 0b1011
    return v
A8 = [[v ^ 1 for v in range(8)], [v ^ 2 for v in range(8)], [v ^ 4 for v in range(8)], [m8(v) for v in range(8)]]
out.append(("AGL1-8", spec(8, A8), 56))
with open("queue4.txt", "w") as f:
    for name, s, o in out:
        for k in range(2, 400):
            if 254 <= o*k <= 330:
                f.write(f"{s} x cyc {k}\n")
        if 254 <= o <= 330:
            f.write(s + "\n")
for name, s, o in out:
    print(name, o, s[:60])

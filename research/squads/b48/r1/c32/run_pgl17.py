import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r1/c32')
import cosetgen as cg
# PGL(2,17) acting on projective line 0..16, inf = 17
p = 17; INF = 17; d = 18
def inv(x):
    return pow(x, p - 2, p)
def mob(f):
    return tuple(f(i) for i in range(d))
t = mob(lambda x: INF if x == INF else (x + 1) % p if x != INF else INF)
t = tuple((x + 1) % p if x < p else INF for x in range(d))
m3 = tuple((3 * x) % p if x < p else INF for x in range(d))
def iv(x):
    if x == INF: return 0
    if x == 0: return INF
    return inv(x)
j = tuple(iv(x) for x in range(d))
if __name__ == '__main__':
    cg.run('PGL2_17', [t, m3, j], d, budget=45, nA=40, seed=1, outdir='/home/user/degree-diameter/research/squads/b48/r1/c32')

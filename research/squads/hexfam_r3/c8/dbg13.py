import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
G = Geo(13); N, L = G.N, G.L; LP, PL = G.LP, G.PL
pairs = [tuple(map(int, l.split())) for l in open('disj13_try1.pairs') if l.strip()]
R = [p[0] for p in pairs[:792]]; Rs = [p[1] for p in pairs[:792]]
X = [p[0] for p in pairs[792:]]; S = [p[1] for p in pairs[792:]]
def dist4_lines(s):
    M = PL[LP[s]].ravel(); M = M[M != s]
    m = np.zeros(L, bool); m[PL[LP[M]].ravel()] = True; m[s] = True
    return m, M
for k, (x, s) in enumerate(zip(X, S)):
    m, M = dist4_lines(s)
    bx = (G.B(G.C[[x]], G.C[R])[0] == 0)
    lineflag = m[Rs]
    bad = np.nonzero(bx != lineflag)[0]
    print('x', k, 'mismatches', len(bad), 'conc-lines of s among Rs:', int(np.isin(Rs, M).sum()), 'r-in-N(x)', int(bx.sum()), 'line-near', int(lineflag.sum()))
    if len(bad):
        i = bad[0]; print('  e.g. R index', i, 'Rs', Rs[i], 'd(line)<=4', lineflag[i], 'B==0', bx[i], 'in M(conc)', Rs[i] in set(M.tolist()))

# group elements of G2(5) on H(5): matrices -> permutations on points (0..P-1) and lines (P..P+L-1)
import pickle
from g2lie import *
allpts, lines = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/hexdata.pkl', 'rb'))
P = len(allpts); L = len(lines)
idx = {v: i for i, v in enumerate(allpts)}
lidx = {l: i for i, l in enumerate(lines)}
inv2 = pow(2, p-2, p)
def norm(v):
    for x in v:
        if x % p:
            inv = pow(x, p-2, p); return tuple((y*inv) % p for y in v)
def perm_of(g):
    # g: 7x7 matrix; returns list of length P+L
    pp = [0]*P
    for i, v in enumerate(allpts):
        w = [sum(g[r][c]*v[c] for c in range(N)) % p for r in range(N)]
        pp[i] = idx[norm(w)]
    lp = [0]*L
    for k, l in enumerate(lines):
        lp[k] = lidx[tuple(sorted(pp[z] for z in l))]
    return pp + [P + x for x in lp]
def is_aut(perm):
    # check incidence preservation: point-line flags -> sample check on lines
    for k, l in enumerate(lines):
        img = set(perm[z] for z in l)
        if perm[P + k] - P not in range(L): return False
        if set(lines[perm[P + k] - P]) != img: return False
    return True
def mat_mul(A, B): return [[sum(A[i][t]*B[t][j] for t in range(N)) % p for j in range(N)] for i in range(N)]
def unip(e):
    e2 = mat_mul(e, e)
    return [[(int(i == j) + e[i][j] + inv2*e2[i][j]) % p for j in range(N)] for i in range(N)]
def load_root_elems():
    data = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/nilp.pkl', 'rb'))
    return [d[2] for d in data]

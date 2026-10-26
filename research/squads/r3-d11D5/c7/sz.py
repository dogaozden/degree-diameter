"""Find collineations of W(8) that commute with the polarity delta: linear maps in PGL(4,8) that preserve the
Suzuki-Tits ovoid O = absolute points of delta (expected: Sz(8) = centralizer of delta).  Random frame-to-frame
search, then random words in the found elements; output permutations of the 585 points and lines (json).
usage: python3 sz.py seed count out.json"""
import sys, json, random, os
D = "/home/user/degree-diameter/research/d11D5"
W = json.load(open(os.path.join(D, "w8.json")))
pts = [tuple(p) for p in W["points"]]; L = [list(s) for s in W["lines"]]
n = len(pts); idx = {p: i for i, p in enumerate(pts)}
d_pt, d_ln = W["klein_pt"], W["klein_ln"]          # delta = klein o frob (polarity_m = 1)
fp, fl = W["frob_pt"], W["frob_ln"]
d_pt = [d_pt[fp[p]] for p in range(n)]            # m = 1: fpm = frob_pt
d_ln = [d_ln[fl[l]] for l in range(n)]
lidx = {frozenset(s): i for i, s in enumerate(L)}
O = [p for p in range(n) if p in L[d_pt[p]]]
Oset = set(O)
assert len(O) == 65, len(O)
# GF(8) with x^3 + x + 1
def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a & 8: a ^= 0b1011
    return r
MUL = [[gmul(a, b) for b in range(8)] for a in range(8)]
INV = [0] + [next(b for b in range(1, 8) if MUL[a][b] == 1) for a in range(1, 8)]
def norm(v):
    for c in v:
        if c:
            s = INV[c]; return tuple(MUL[s][x] for x in v)
    return None
def matvec(M, v):
    return tuple(MUL[M[i][0]][v[0]] ^ MUL[M[i][1]][v[1]] ^ MUL[M[i][2]][v[2]] ^ MUL[M[i][3]][v[3]] for i in range(4))
def matmul(A, B):
    return [[MUL[A[i][0]][B[0][j]] ^ MUL[A[i][1]][B[1][j]] ^ MUL[A[i][2]][B[2][j]] ^ MUL[A[i][3]][B[3][j]] for j in range(4)] for i in range(4)]
def inv4(A):
    M = [row[:] + [1 if i == j else 0 for j in range(4)] for i, row in enumerate(A)]
    for c in range(4):
        piv = next((r for r in range(c, 4) if M[r][c]), None)
        if piv is None: return None
        M[c], M[piv] = M[piv], M[c]
        s = INV[M[c][c]]; M[c] = [MUL[s][x] for x in M[c]]
        for r in range(4):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [M[r][j] ^ MUL[f][M[c][j]] for j in range(8)]
    return [row[4:] for row in M]
def frame_matrix(s):   # s: 5 points in general position -> P with P e_i ~ s_i, P (1,1,1,1) ~ s_5
    S = [[s[j][i] for j in range(4)] for i in range(4)]     # columns s_0..s_3
    Si = inv4(S)
    if Si is None: return None
    lam = [0] * 4
    for i in range(4):
        lam[i] = 0
    lam = [0, 0, 0, 0]
    v = matvec(Si, s[4])
    if any(x == 0 for x in v): return None
    return [[MUL[S[i][j]][v[j]] for j in range(4)] for i in range(4)]
def perm_of(M):
    pp = []
    for p in range(n):
        y = norm(matvec(M, pts[p]))
        pp.append(idx[y])
    return pp
def check(pp):
    if len(set(pp)) != n: return False
    ll = []
    for s in L:
        t = frozenset(pp[x] for x in s)
        if t not in lidx: return False
        ll.append(lidx[t])
    return all(ll[d_pt[p]] == d_pt[pp[p]] for p in range(n))
def line_perm(pp):
    return [lidx[frozenset(pp[x] for x in s)] for s in L]
def order(pp):
    from math import gcd
    seen = [False] * n; o = 1
    for p in range(n):
        if not seen[p]:
            c = 0; q = p
            while not seen[q]: seen[q] = True; q = pp[q]; c += 1
            o = o * c // gcd(o, c)
    return o
if __name__ == "__main__":
    seed, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    found = []
    tries = 0
    src = None
    while src is None:
        s = rng.sample(O, 5)
        Ps = frame_matrix([pts[x] for x in s])
        if Ps is not None: src = (s, Ps, inv4(Ps))
    s, Ps, Psi = src
    while len(found) < count and tries < 3000000:
        tries += 1
        t = rng.sample(O, 5)
        Pt = frame_matrix([pts[x] for x in t])
        if Pt is None: continue
        M = matmul(Pt, Psi)
        ok = True
        for x in O[:12]:
            if norm(matvec(M, pts[x])) not in pts or idx[norm(matvec(M, pts[x]))] not in Oset: ok = False; break
        if not ok: continue
        if any(idx[norm(matvec(M, pts[x]))] not in Oset for x in O): continue
        pp = perm_of(M)
        if check(pp):
            found.append(pp)
            print("found", len(found), "tries", tries, "order", order(pp), flush=True)
    # random words in the found group
    gens = found[:]
    def mulp(a, b): return [a[b[i]] for i in range(n)]
    G = []
    cur = list(range(n))
    for _ in range(400):
        w = list(range(n))
        for _ in range(12):
            w = mulp(w, rng.choice(gens))
        G.append(w)
    lines_out = {}
    for w in G + gens:
        o = order(w)
        lines_out.setdefault(o, 0)
        lines_out[o] += 1
    print("order distribution", sorted(lines_out.items()), flush=True)
    keep = []
    for w in G:
        o = order(w)
        if o in (5, 7, 13, 2, 4) and check(w):
            keep.append({"order": o, "pt": w, "ln": line_perm(w)})
    json.dump({"gens": [{"pt": g, "ln": line_perm(g), "order": order(g)} for g in gens], "elems": keep}, open(out, "w"))
    print("saved", len(keep), "elements of order 2,4,5,7,13; gens", len(gens))

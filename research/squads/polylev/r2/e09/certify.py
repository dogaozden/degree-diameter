"""certify.py HEXBIN LINESFILE: independent check of a set of disjoint totally singular lines of Q(6,q).
Own GF(q) arithmetic (prime q: mod p; q = 8: GF(2)[x]/(x^3+x+1), bits = coefficients), own parsing of the hex file.
Checks: each class has q+1 distinct point ids; each point singular (x0x4+x1x5+x2x6-x3^2=0); pairwise orthogonal
within a class (b=0); rank of the class's coordinate matrix is 2 (so the q+1 points are a full projective line);
classes pairwise disjoint (no point id used twice). Also checks the hex file's own hexagon lines pass the same test
(sanity check of the arithmetic). Prints a JSON line with the certified count."""
import sys, json
import numpy as np

hexpath, linespath = sys.argv[1], sys.argv[2]
with open(hexpath, 'rb') as f:
    q, N, Lh = np.frombuffer(f.read(12), dtype=np.int32)
    q, N, Lh = int(q), int(N), int(Lh)
    hlines = np.frombuffer(f.read(4 * Lh * (q + 1)), dtype=np.int32).reshape(Lh, q + 1).astype(np.int64)
    coord = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)

# GF(q) tables, built here (not from hexlib)
if q == 7 or q == 3 or q == 5 or q == 11 or q == 13 or q == 2:
    ADD = np.add.outer(np.arange(q), np.arange(q)) % q
    MUL = np.multiply.outer(np.arange(q), np.arange(q)) % q
elif q == 8:
    def gf8mul(a, b):
        r = 0
        for i in range(3):
            if (b >> i) & 1:
                r ^= a << i
        for k in (4, 3):
            if (r >> k) & 1:
                r ^= 0b1011 << (k - 3)
        return r
    ADD = np.array([[a ^ b for b in range(8)] for a in range(8)])
    MUL = np.array([[gf8mul(a, b) for b in range(8)] for a in range(8)])
else:
    raise SystemExit('unsupported q')
NEG = np.array([int(np.where(ADD[a] == 0)[0][0]) for a in range(q)])
# sanity: field axioms on a sample (distributivity, inverses)
for a in range(q):
    for b in range(q):
        for c in range(q):
            assert MUL[a, ADD[b, c]] == ADD[MUL[a, b], MUL[a, c]], 'field law fails'
assert all(any(MUL[a, b] == 1 for b in range(q)) for a in range(1, q)), 'not a field'

def f_add(a, b): return ADD[a, b]
def f_mul(a, b): return MUL[a, b]

def Qval(x):
    s = ADD[ADD[MUL[x[0], x[4]], MUL[x[1], x[5]]], MUL[x[2], x[6]]]
    return ADD[s, NEG[MUL[x[3], x[3]]]]

def bval(x, y):
    s = 0
    for i, j in ((0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)):
        s = ADD[s, MUL[x[i], y[j]]]
    t = MUL[x[3], y[3]]
    t2 = ADD[t, t]                      # 2 t (zero in characteristic 2)
    return ADD[s, NEG[t2]]

def rank(M):
    M = M.copy(); r = 0
    for c in range(M.shape[1]):
        piv = next((i for i in range(r, M.shape[0]) if M[i, c]), None)
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        inv = next(b for b in range(1, q) if MUL[M[r, c], b] == 1)
        M[r] = [MUL[inv, v] for v in M[r]]
        for i in range(M.shape[0]):
            if i != r and M[i, c]:
                M[i] = [ADD[M[i, k], NEG[MUL[M[i, c], M[r, k]]]] for k in range(M.shape[1])]
        r += 1
    return r

def check_class(ids):
    ids = [int(t) for t in ids]
    if len(ids) != q + 1 or len(set(ids)) != q + 1: return 'not q+1 distinct ids'
    X = coord[ids]
    for x in X:
        if Qval(x) != 0: return 'point not singular'
    for i in range(q + 1):
        for j in range(i + 1, q + 1):
            if bval(X[i], X[j]) != 0: return 'not orthogonal'
    if rank(X) != 2: return 'rank not 2'
    return None

# sanity on the hexagon's own lines
bad_h = sum(1 for l in range(Lh) if check_class(hlines[l]) is not None)
print(f'sanity: hexagon lines of H(q) failing the test: {bad_h} of {Lh}', file=sys.stderr)

S = np.fromfile(linespath, dtype=np.int32).astype(np.int64).reshape(-1, q + 1)
seen = set()
K = 0; errs = {}
for row in S:
    e = check_class(row)
    if e is None:
        ids = [int(t) for t in row]
        if any(t in seen for t in ids):
            e = 'not disjoint from earlier classes'
        else:
            seen.update(ids)
    if e is None:
        K += 1
    else:
        errs[e] = errs.get(e, 0) + 1
print(json.dumps({'file': linespath, 'q': q, 'listed': int(len(S)), 'certified': K, 'errors': errs,
                  'points_covered': len(seen), 'pct_points': round(100 * len(seen) / N, 2)}))

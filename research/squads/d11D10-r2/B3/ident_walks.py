# B3: formal word identities of short non-backtracking walks on the Haar graph H(G,S), G = PSL(2,243) x Z_11.
# Letters: e (the fixed generator) and the orbit of a generator u under alpha.  A walk l_1..l_L (l_{t+1} != l_t) has
# B-side value l_L ... l_1 with signs alternating (odd L).  Two walks are a formal identity when their values agree for
# every orbit generator; we test this on K random generators (accidental agreement has probability ~ N^-K).
# usage: ident_walks.py MODE K MAXLEN SEED      MODE = k10 (h-conjugate orbit, order 10) | k5 (Frobenius, two orbits)
import sys, random, collections
MODE, K, MAXL, SEED = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rnd = random.Random(SEED)
# GF(243) = GF(3)[t]/(t^5 + 2t + 1); element = sum c_i 3^i (as haar_sym writes it); t^5 = t + 2 (mod 3)
def pmul(a, b):
    ca = [(a // 3**i) % 3 for i in range(5)]; cb = [(b // 3**i) % 3 for i in range(5)]
    r = [0] * 9
    for i in range(5):
        for j in range(5): r[i + j] = (r[i + j] + ca[i] * cb[j]) % 3
    for d in range(8, 4, -1):          # t^d = t^(d-4) + 2 t^(d-5)
        c = r[d]
        if c:
            r[d] = 0; r[d - 4] = (r[d - 4] + c) % 3; r[d - 5] = (r[d - 5] + 2 * c) % 3
    return sum(r[i] * 3**i for i in range(5))
MUL = [[pmul(a, b) for b in range(243)] for a in range(243)]
ADD = [[sum((((a // 3**i) + (b // 3**i)) % 3) * 3**i for i in range(5)) for b in range(243)] for a in range(243)]
NEG = [sum(((3 - (a // 3**i)) % 3) * 3**i for i in range(5)) for a in range(243)]
# field sanity: every nonzero element has an inverse
INV = [None] * 243
for a in range(1, 243):
    for b in range(1, 243):
        if MUL[a][b] == 1: INV[a] = b; break
assert all(INV[a] is not None for a in range(1, 243)), "not a field"
def mmul(A, B):
    a1, b1, c1, d1 = A; a2, b2, c2, d2 = B
    return (ADD[MUL[a1][a2]][MUL[b1][c2]], ADD[MUL[a1][b2]][MUL[b1][d2]],
            ADD[MUL[c1][a2]][MUL[d1][c2]], ADD[MUL[c1][b2]][MUL[d1][d2]])
def canon(M):   # PSL(2,243): identify M with -M
    nM = tuple(NEG[x] for x in M); return min(M, nM)
def gmul(g, h):
    return (canon(mmul(g[0], h[0])), (g[1] + h[1]) % 11)
def ginv(g):
    a, b, c, d = g[0]; return (canon((d, NEG[b], NEG[c], a)), (-g[1]) % 11)
ID = ((1, 0, 0, 1), 0)
FROB = lambda x: MUL[MUL[x][x]][x]          # x -> x^3 on entries
H = (0, 1, 2, 0); HI = (0, 2, 1, 0)           # h and h^-1 (det 1 mod 3 both)
def conj_h(M):
    return canon(mmul(mmul(H, M), HI))
def alpha_k10(g):   # z -> 2z, Q-part conj(h) o Frobenius
    M, z = g; F = tuple(FROB(x) for x in M); return (conj_h(F), (2 * z) % 11)
def alpha_k5(g):    # z -> 3z, Q-part Frobenius
    M, z = g; return (canon(tuple(FROB(x) for x in M)), (3 * z) % 11)
def rand_g():
    while True:
        a, b, c = rnd.randrange(243), rnd.randrange(243), rnd.randrange(243)
        if a == 0: continue
        d = MUL[ADD[1][MUL[b][c]]][INV[a]]           # ad - bc = 1 -> d = (1 + bc)/a (sign: bc = -bc mod 3 handled below)
        M = (a, b, c, d)
        # verify determinant 1
        det = ADD[MUL[a][d]][NEG[MUL[b][c]]]
        if det == 1: return (canon(M), rnd.randrange(1, 11))
# sanity: alpha is a homomorphism of G, alpha^10 = id (k10) / alpha^5 = id (k5), and alpha^5 = (c_h, -1) for k10
def check(alpha, order):
    for _ in range(4):
        g, h = rand_g(), rand_g()
        assert alpha(gmul(g, h)) == gmul(alpha(g), alpha(h)), "not a homomorphism"
        y = g
        for _ in range(order): y = alpha(y)
        assert y == g, "alpha^order != 1"
if MODE == 'k10':
    alpha, order, norb = alpha_k10, 10, 1
    check(alpha, 10)
    for _ in range(4):   # alpha^5 = (conjugation by h, z -> -z), so the orbit has h-conjugate pairs s_(i+5) = (h x_i h^-1, -z_i)
        g = rand_g(); y = g
        for _ in range(5): y = alpha(y)
        assert y == (canon(mmul(mmul(H, g[0]), HI)), (-g[1]) % 11), "alpha^5 is not (c_h, -1)"
else:
    alpha, order, norb = alpha_k5, 5, 2
    check(alpha, 5)
# generators: K samples; letters per sample = [e] + orbits
samples = []
for _ in range(K):
    gens = [rand_g() for _ in range(norb)]
    letters = [ID]
    for u in gens:
        y = u
        for i in range(order):
            letters.append(y); y = alpha(y)
    samples.append(letters)
NL = len(samples[0])                  # 1 + order*norb letters, letter 0 = e
names = ['e'] + ['%s%d' % ('o' if norb == 1 else ('p' if i < order else 'q'), (i % order)) for i in range(order * norb)]
# inverse table per sample
inv_s = [[ginv(l) for l in L] for L in samples]
# DFS over non-backtracking walks; record values per length (odd lengths = B-side)
values = collections.defaultdict(list)      # key -> list of (length, walk)
count_len = collections.Counter()
walk = []
def dfs(vals, side, last, depth):
    # vals: list of K group elements (current end vertex (v, side)); depth = steps taken
    if depth > 0 and side == 1:        # B-side element reached after odd number of steps
        key = tuple(vals)
        values[key].append((depth, tuple(walk)))
        count_len[depth] += 1
    if depth == MAXL: return
    for l in range(NL):
        if l == last: continue
        walk.append(l)
        if side == 0:   # A -> B: v <- l v
            nv = [gmul(samples[k][l], vals[k]) for k in range(K)]
            dfs(nv, 1, l, depth + 1)
        else:           # B -> A: v <- l^-1 v
            nv = [gmul(inv_s[k][l], vals[k]) for k in range(K)]
            dfs(nv, 0, l, depth + 1)
        walk.pop()
dfs([ID] * K, 0, -1, 0)
tot = sum(count_len.values())
print("mode %s K=%d maxlen=%d seed=%d letters=%d" % (MODE, K, MAXL, SEED, NL))
print("B-side walks by length:", dict(sorted(count_len.items())))
distinct = len(values)
dup_groups = [v for v in values.values() if len(v) > 1]
print("total walks %d, distinct values (all %d samples) %d, duplicated walks %d in %d groups" % (
    tot, K, distinct, tot - distinct, len(dup_groups)))
byL = collections.Counter()
for v in values.values():
    if len(v) > 1:
        byL[tuple(sorted(set(l for l, _ in v)))] += len(v) - 1
print("duplicates by set of lengths:", dict(byL))
def show(w):
    return ' '.join(names[l] for l in w)
ex = sorted(dup_groups, key=lambda v: (len(v[0][1]) if False else v[0][0], -len(v)))
for v in ex[:40]:
    print("  identical:", ' | '.join('[%s]' % show(w) for _, w in v))

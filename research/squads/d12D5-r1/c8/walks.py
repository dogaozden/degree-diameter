# walk statistics per target for the record chart: nonbacktracking 4-walks from one A-vertex, grouped by endpoint
import sys, itertools, collections
G = '/home/user/degree-diameter/research/d12D5/graphs/'
ctrl = [tuple(map(int, l.split())) for l in open(G + 'd12D5_n10692_k33m_z22e_controller.txt') if l.strip()]
ech = [list(map(int, l.split())) for l in open(G + 'd12D5_n10692_k33m_z22e_echart.txt') if l.strip()]
m = max(r[0] for r in ctrl) + 1
vecs = list(itertools.product(range(3), repeat=4))
def rank3(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        p = next((i for i in range(r, len(rows)) if rows[i][c] % 3), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 if rows[r][c] % 3 == 1 else 2
        rows[r] = [(x * inv) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % 3:
                f = rows[i][c]; rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r])]
        r += 1
    return r
def mat(e):
    A = [[x % 3 for x in ech[e][4*i:4*i+4]] for i in range(4)]; b = [x % 3 for x in ech[e][16:20]]
    return A, b
def inv(A):
    n = 4; M = [list(A[i]) + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] % 3); M[c], M[p] = M[p], M[c]
        iv = 1 if M[c][c] == 1 else 2; M[c] = [(x * iv) % 3 for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]: f = M[r][c]; M[r] = [(x - f * y) % 3 for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]
def mv(M, v): return tuple(sum(M[i][j] * v[j] for j in range(4)) % 3 for i in range(4))
AB = [mat(e) for e in range(len(ech))]
AI = [inv(A) for A, b in AB]
cv = [mv(AI[e], AB[e][1]) for e in range(len(ech))]
adjA = collections.defaultdict(list); adjB = collections.defaultdict(list)
for a, b, e in ctrl: adjA[a].append((b, e)); adjB[b].append((a, e))
# base vertex of controller vertex: block = v // 22 (n = 22 for the record)
n = 22
res = collections.Counter(); sing = collections.Counter(); tot = collections.Counter()
s0 = 0
for b1, e1 in adjA[s0]:
    for a2, e2 in adjB[b1]:
        if e2 == e1: continue
        for b3, e3 in adjA[a2]:
            if e3 == e2: continue
            for a4, e4 in adjB[b3]:
                if e4 == e3: continue
                v = [mv(AI[e2], AB[e1][1]), cv[e2], cv[e3], mv(AI[e3], AB[e4][1])]
                ok = rank3(v) == 4
                tot[a4] += 1; sing[a4] += (not ok)
print('record m =', m, 'walks from A-vertex 0:', sum(tot.values()), 'targets reached:', len(tot), 'of', m)
cnt = collections.Counter(tot[c] for c in range(m))
print('nonbacktracking 4-walks per A-target (count: #targets):', sorted(cnt.items()))
print('singular 4-walks per A-target (total):', sum(sing.values()), 'targets with all walks singular:', sum(1 for c in range(m) if tot[c] and sing[c] == tot[c]))
print('mean walks per target:', round(sum(tot.values()) / m, 3))

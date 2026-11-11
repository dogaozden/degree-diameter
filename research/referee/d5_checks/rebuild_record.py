"""Rebuild the (13,5) graph of sec. 11 from its solution file using only Definitions 2.1 and 3.1 of the note,
with my own W(9) (gq.W), and check every hypothesis the note uses (Lemma 1.1 spread, relaxed set, Prop. 6.4
local dualities, slot bookkeeping, the A-hub rule of Prop. 7.2, hub degrees). Writes the edge list for bfs.c.
Usage: python3 rebuild_record.py SOLUTION.json OUT.edges"""
import json, sys, itertools
from gf import GF
from gq import W

sol = json.load(open(sys.argv[1]))
q, r, types = sol['q'], sol['r'], sol['types']
F = GF(q)                      # same encoding as the file (checked separately: x^2+1 for q = 9)
Wq = W(F)
N = Wq.N
# map the file's points to mine by coordinates, and check the file's lines are exactly the lines of my W(q)
fp = [Wq.idx[tuple(c)] for c in sol['W_points']]
assert len(set(fp)) == N
mylines = {tuple(l): i for i, l in enumerate(Wq.lp)}
fl = [mylines[tuple(sorted(fp[x] for x in l))] for l in sol['W_lines']]
assert len(set(fl)) == N
print("file's W(%d): %d points and %d lines = my W(%d)" % (q, N, N, q))
# work in the file's indices: Q(4,q) = W(q)^D, point i of Q = file line i, line j of Q = file point j
Wlines = [set(l) for l in sol['W_lines']]              # Q-point i  <-> set of W-points (= Q-lines) on it
Q_pts_on_line = [[] for _ in range(N)]                 # Q-line j (W-point j) -> Q-points (W-lines through it)
for i, l in enumerate(Wlines):
    for p in l:
        Q_pts_on_line[p].append(i)
Q_lines_on_pt = [sorted(l) for l in Wlines]
def coll_Q(a, b):        # Q-points a, b (W-lines) collinear in Q iff the W-lines meet
    return a != b and bool(Wlines[a] & Wlines[b])
Wcoll = [set() for _ in range(N)]                       # W-points collinear in W  <-> Q-lines concurrent
for l in Wlines:
    for a in l:
        Wcoll[a] |= l - {a}
G2_pt = [set() for _ in range(N)]                       # Gamma_2 of Q-points
for j in range(N):
    for a in Q_pts_on_line[j]:
        G2_pt[a] |= set(Q_pts_on_line[j]) - {a}
G2_line = Wcoll                                         # Gamma_2 of Q-lines

nlev = 2 * r + 1
assert len(types) == nlev and set(types) <= set('HD')
arcs = [tuple(a) for a in sol['arcs']]
# rotational tournament j -> j+1..j+r, every pair once, r out-arcs per level
assert sorted(arcs) == sorted((j, (j + k) % nlev) for j in range(nlev) for k in range(1, r + 1))
# elements: Q-points are 'P', Q-lines are 'L'
A = {'H': 'P', 'D': 'L'}; B = {'H': 'L', 'D': 'P'}
def vid(j, typ, e):
    return j * 2 * N + (e if typ == 'P' else N + e)

O = sol['ovoid_Q4']; T = sol['T']
assert len(set(O)) == len(O) == q * q + 1
# O = q^2+1 pairwise disjoint W-lines (a spread of W(q)) = pairwise non-collinear Q-points (ovoid of Q(4,q))
assert all(not coll_Q(a, b) for a, b in itertools.combinations(O, 2))
# is it the spread of Lemma 1.1 for some (alpha, beta)?
coords = [tuple(c) for c in sol['W_points']]
fidx = {c: i for i, c in enumerate(coords)}
def lemma11(al, be):
    from gf import span_points
    m, a_ = F.mul, F.add
    lines = [frozenset(fidx[z] for z in span_points(F, (0, 0, 1, 0), (0, 0, 0, 1)))]
    for a in range(q):
        for b in range(q):
            x = (1, 0, a, b); y = (0, 1, b, a_[m[al][a]][m[be][b]])
            lines.append(frozenset(fidx[z] for z in span_points(F, x, y)))
    return lines
Oset = {frozenset(Wlines[i]) for i in O}
found = []
for al in range(q):
    for be in range(q):
        if all(F.sub[F.sub[F.mul[t][t]][F.mul[be][t]]][al] for t in range(q)):
            if set(lemma11(al, be)) == Oset:
                found.append((al, be))
print("ovoid: %d pairwise non-collinear points of Q(4,%d); equals the spread of Lemma 1.1 for (alpha,beta) in %s"
      % (len(O), q, found))
# T: relaxed set of Q-lines (W-points), every line meets at most one other; meeting point not in O
Ts = set(T)
partner = {}
for l in T:
    ms = [m for m in Wcoll[l] if m in Ts]
    assert len(ms) <= 1, (l, ms)
    if ms:
        partner[l] = ms[0]
pairs = {frozenset((l, m)) for l, m in partner.items()}
zin = 0
for pr in pairs:
    l, m = tuple(pr)
    z = [i for i in range(N) if l in Wlines[i] and m in Wlines[i]]   # the Q-point l /\ m (W-line joining them)
    assert len(z) == 1
    zin += z[0] in set(O)
print("T: %d lines, %d partner pairs, %d partnered lines, meeting points in O: %d" % (len(T), len(pairs), len(partner), zin))

# matchings and freed sets per arc
M = {}; R = {}
for (j, k) in arcs:
    tj, tk = types[j], types[k]
    if tj != tk:                          # friendly: M = id, R = O (H->D, points) or T (D->H, lines)
        assert A[tj] == B[tk]
        M[(j, k)] = list(range(N)); R[(j, k)] = list(O) if tj == 'H' else list(T)
    else:
        nf = sol['nonfriendly']['%d,%d' % (j, k)]
        Mt = nf['M']; Rt = nf['R']
        assert sorted(Mt) == list(range(N))
        M[(j, k)] = Mt; R[(j, k)] = Rt
        # check Prop. 6.4 hypotheses (H1), (H3) on R
        G2A = G2_pt if A[tj] == 'P' else G2_line
        G2B = G2_line if B[tk] == 'L' else G2_pt
        assert len(Rt) == 2 and Rt[1] not in G2A[Rt[0]], "H1"
        for x in Rt:
            assert {Mt[a] for a in G2A[x]} == G2B[Mt[x]], "H3"
print("non-friendly arcs: %d, each a 2-element non-collinear freed set with (H1),(H3)" %
      sum(types[j] == types[k] for j, k in arcs))

edges = []
for j in range(nlev):                      # level edges
    for p in range(N):
        for l in Q_lines_on_pt[p]:
            edges.append((vid(j, 'P', p), vid(j, 'L', l)))
for (j, k) in arcs:                        # matching edges minus freed
    Rs = set(R[(j, k)])
    for a in range(N):
        if a not in Rs:
            edges.append((vid(j, A[types[j]], a), vid(k, B[types[k]], M[(j, k)][a])))
alpha = [sum(len(R[(j, k)]) for (jj, k) in arcs if jj == j) for j in range(nlev)]
beta = [sum(len(R[(i, j)]) for (i, jj) in arcs if jj == j) for j in range(nlev)]
print("alpha =", alpha, " beta =", beta)

nlevel = nlev * 2 * N
KB, KA = sol['K_B'], sol['K_A']
assert KB <= min(alpha) and KA <= min(beta)
usedA = set(); usedB = set()
Bslot_hub = {}; Aslot_hub = {}
for h, slots in enumerate(sol['Bhub_slots']):          # B-hub takes a free A-slot in every level
    assert sorted(s[0] for s in slots) == list(range(nlev))
    for (j, e, arc) in slots:
        arc = tuple(arc); assert arc[0] == j and e in set(R[arc])
        assert (arc, e) not in usedA; usedA.add((arc, e))
        edges.append((nlevel + h, vid(j, A[types[j]], e)))
for g, slots in enumerate(sol['Ahub_slots']):          # A-hub takes a free B-slot in every level
    assert sorted(s[0] for s in slots) == list(range(nlev))
    for (j, e, arc) in slots:
        arc = tuple(arc); assert arc[1] == j
        x = [a for a in R[arc] if M[arc][a] == e]; assert len(x) == 1     # e = M_t(x), x freed
        assert (arc, x[0]) not in usedB; usedB.add((arc, x[0]))
        Aslot_hub[(arc, e)] = g
        edges.append((nlevel + KB + g, vid(j, B[types[j]], e)))
ydeg_B = [0] * KB; ydeg_A = [0] * KA
for (h, g) in sol['Y']:
    edges.append((nlevel + h, nlevel + KB + g)); ydeg_B[h] += 1; ydeg_A[g] += 1
print("hubs %d + %d, Y: %d edges, max Y-degree B %d, A %d (q - r = %d)" %
      (KB, KA, len(sol['Y']), max(ydeg_B), max(ydeg_A), q - r))
# A-hub rule (Prop. 7.2): for each D->H arc t=(j->k) and partnered l, the A-hub on slot (l,t) at (l,k)
# has its level-j slot at a point (of Q) on the partner m
ok = bad = untaken = 0
Aslot_level = {}
for g, slots in enumerate(sol['Ahub_slots']):
    for (j, e, arc) in slots:
        Aslot_level[(g, j)] = e
for (j, k) in arcs:
    if types[j] == 'D' and types[k] == 'H':
        for l in partner:
            g = Aslot_hub.get(((j, k), l))
            if g is None:
                untaken += 1; continue
            pt = Aslot_level[(g, j)]               # a Q-point = W-line index
            if partner[l] in Wlines[pt]:           # Q-point pt on Q-line m  <=>  W-point m on W-line pt
                ok += 1
            else:
                bad += 1
print("A-hub rule: satisfied %d, violated %d, partnered slot not taken by any hub %d" % (ok, bad, untaken))
n = nlevel + KB + KA
with open(sys.argv[2], 'w') as f:
    f.write("%d\n" % n)
    for u, v in edges:
        f.write("%d %d\n" % (u, v))
print("n = %d = %d*2*%d + %d + %d, edges %d" % (n, nlev, N, KB, KA, len(edges)))

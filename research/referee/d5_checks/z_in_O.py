"""Section 7, 'The hubs exist': is the requirement z not in O needed?  Seven levels HHHDHHD over Q(4,q), ovoid O
on H->D, on D->H the partial spread of Lemma 1.3 plus one line m meeting one of its lines l at the ovoid point
z = o_l (so the pair (l, m) has z in O), Prop. 6.4 on the non-friendly arcs, K_B = K_A = 2 hubs joined by K_{2,2}.
The two A-hubs follow the hub rule of Prop. 7.2 with BOTH level-3 slots and BOTH level-6 slots at z
(z has three free B-slots in level 3 and two in level 6).  Variant 'break': g_m's level-3 slot off l.
Usage: python3 z_in_O.py q OUT [break]"""
import sys, random
from gf import GF
from gq import W, Q4
from families import lemma11_spread, lemma13_partial_ovoid, klein, local_duality
q = int(sys.argv[1]); out = sys.argv[2]; brk = len(sys.argv) > 3
rng = random.Random(11)
F = GF(q); Wq = W(F); G = Q4(F); N = G.N
lp, pl = klein(F, Wq, G)
O = [lp[l] for l in lemma11_spread(F, Wq)]; Oset = set(O)
T = [pl[p] for p in lemma13_partial_ovoid(F, Wq, rng)]
def pick():
    for l in T:
        z = next(p for p in G.lp[l] if p in Oset)
        for mm in G.pl[z]:
            if mm != l and all(t == l or t not in G.meets[mm] for t in T):
                return l, z, mm
l, z, m = pick()
T = T + [m]
types = 'HHHDHHD'; r = 3; nlev = 7
arcs = [(j, (j + k) % nlev) for j in range(nlev) for k in range(1, r + 1)]
A = {'H': 'P', 'D': 'L'}; B = {'H': 'L', 'D': 'P'}
vid = lambda j, t, e: j * 2 * N + (e if t == 'P' else N + e)
M = {}; R = {}
for (j, k) in arcs:
    if types[j] != types[k]:
        M[(j, k)] = list(range(N)); R[(j, k)] = O if types[j] == 'H' else T
    else:
        M[(j, k)], R[(j, k)] = local_duality(G, A[types[j]], rng)
edges = []
for j in range(nlev):
    for li in range(N):
        for p in G.lp[li]:
            edges.append((vid(j, 'P', p), vid(j, 'L', li)))
freeA = {j: [] for j in range(nlev)}; freeB = {j: [] for j in range(nlev)}
for (j, k) in arcs:
    for a in range(N):
        if a in set(R[(j, k)]):
            freeA[j].append(((j, k), a)); freeB[k].append(((j, k), M[(j, k)][a]))
        else:
            edges.append((vid(j, A[types[j]], a), vid(k, B[types[k]], M[(j, k)][a])))
base = nlev * 2 * N
# A-hubs g_l (index 0) and g_m (index 1): slot (x, t) at the H level k for every D->H arc t = (j -> k)
used = set()
def take(g, j, slot):
    assert slot in freeB[j] and slot not in used; used.add(slot)
    edges.append((base + 2 + g, vid(j, B[types[j]], slot[1])))
for g, x in ((0, l), (1, m)):
    for (j, k) in arcs:
        if types[j] == 'D' and types[k] == 'H':
            take(g, k, ((j, k), x))
# level 3 and 6 slots at z, from different H->D arcs
take(0, 3, ((0, 3), z)); take(1, 3, ((1, 3), z) if not brk else ((1, 3), next(o for o in O if o not in G.lp[l])))
take(0, 6, ((4, 6), z)); take(1, 6, ((5, 6), z))
for h in range(2):                          # B-hubs: any free A-slots
    for j in range(nlev):
        slot = [s for s in freeA[j] if (j, s) not in used][h]; used.add((j, slot))
        edges.append((base + h, vid(j, A[types[j]], slot[1])))
for h in range(2):
    for g in range(2):
        edges.append((base + h, base + 2 + g))
print("q=%d: pair (l,m) meets at z in O: %s; |T| = %d; %s" % (q, z in Oset, len(T), "rule broken for g_m" if brk else "both hubs of the pair at z"))
with open(out, 'w') as f:
    f.write("%d\n" % (base + 4)); f.writelines("%d %d\n" % e for e in edges)
